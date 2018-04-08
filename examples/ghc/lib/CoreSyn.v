(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)



(* Converted imports: *)

Require BasicTypes.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require DataCon.
Require DynFlags.
Require GHC.Base.
Require GHC.Char.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Require Literal.
Require Module.
Require Name.
Require NameEnv.
Require OccName.
Require Panic.
Require TyCon.
Require Util.
Require Var.
Require VarEnv.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive UnfoldingSource : Type
  := InlineRhs : UnfoldingSource
  |  InlineStable : UnfoldingSource
  |  InlineCompulsory : UnfoldingSource.

Inductive UnfoldingGuidance : Type
  := UnfWhen : BasicTypes.Arity -> bool -> bool -> UnfoldingGuidance
  |  UnfIfGoodArgs
   : list GHC.Num.Int -> GHC.Num.Int -> GHC.Num.Int -> UnfoldingGuidance
  |  UnfNever : UnfoldingGuidance.

Inductive TickishScoping : Type
  := NoScope : TickishScoping
  |  SoftScope : TickishScoping
  |  CostCentreScope : TickishScoping.

Inductive TickishPlacement : Type
  := PlaceRuntime : TickishPlacement
  |  PlaceNonLam : TickishPlacement
  |  PlaceCostCentre : TickishPlacement.

Inductive Tickish (id : Type) : Type := Mk_Tickish_Dummy.

Definition OutType :=
  unit%type.

Definition OutKind :=
  unit%type.

Definition OutCoercion :=
  unit%type.

Inductive IsOrphan : Type
  := Mk_IsOrphan : IsOrphan
  |  NotOrphan : OccName.OccName -> IsOrphan.

Definition InType :=
  unit%type.

Definition InKind :=
  unit%type.

Definition InCoercion :=
  unit%type.

Definition CoreBndr :=
  Var.Var%type.

Definition InBndr :=
  CoreBndr%type.

Definition OutBndr :=
  CoreBndr%type.

Inductive TaggedBndr t : Type := TB : CoreBndr -> t -> TaggedBndr t.

Inductive AltCon : Type
  := DataAlt : DataCon.DataCon -> AltCon
  |  LitAlt : Literal.Literal -> AltCon
  |  DEFAULT : AltCon.

Inductive AnnAlt__raw : Type :=.

Reserved Notation "'AnnAlt'".

Inductive AnnExpr__raw : Type :=.

Reserved Notation "'AnnExpr'".

Inductive AnnExpr' bndr annot : Type
  := AnnVar : Var.Id -> AnnExpr' bndr annot
  |  AnnLit : Literal.Literal -> AnnExpr' bndr annot
  |  AnnLam : bndr -> (AnnExpr bndr annot) -> AnnExpr' bndr annot
  |  AnnApp : (AnnExpr bndr annot) -> (AnnExpr bndr annot) -> AnnExpr' bndr annot
  |  AnnCase
   : (AnnExpr bndr annot) ->
     bndr -> unit -> list (AnnAlt bndr annot) -> AnnExpr' bndr annot
  |  AnnLet : (AnnBind bndr annot) -> (AnnExpr bndr annot) -> AnnExpr' bndr annot
  |  AnnCast : (AnnExpr bndr annot) -> (annot * unit)%type -> AnnExpr' bndr annot
  |  AnnTick : (Tickish Var.Id) -> (AnnExpr bndr annot) -> AnnExpr' bndr annot
  |  AnnType : unit -> AnnExpr' bndr annot
  |  AnnCoercion : unit -> AnnExpr' bndr annot
with AnnBind bndr annot : Type
  := AnnNonRec : bndr -> (AnnExpr bndr annot) -> AnnBind bndr annot
  |  AnnRec : list (bndr * AnnExpr bndr annot)%type -> AnnBind bndr annot
where "'AnnExpr'" := (GHC.Base.Synonym AnnExpr__raw (fun bndr_ annot_ =>
                                          (annot_ * AnnExpr' bndr_ annot_)%type%type))
and   "'AnnAlt'" := (GHC.Base.Synonym AnnAlt__raw (fun bndr_ annot_ =>
                                         (AltCon * list bndr_ * AnnExpr bndr_ annot_)%type%type)).

Inductive Alt__raw : Type :=.

Reserved Notation "'Alt'".

Inductive Arg__raw : Type :=.

Reserved Notation "'Arg'".

Inductive Expr b : Type
  := Var : Var.Id -> Expr b
  |  Lit : Literal.Literal -> Expr b
  |  App : (Expr b) -> (Arg b) -> Expr b
  |  Lam : b -> (Expr b) -> Expr b
  |  Let : (Bind b) -> (Expr b) -> Expr b
  |  Case : (Expr b) -> b -> unit -> list (Alt b) -> Expr b
  |  Cast : (Expr b) -> unit -> Expr b
  |  Tick : (Tickish Var.Id) -> (Expr b) -> Expr b
  |  Type_ : unit -> Expr b
  |  Coercion : unit -> Expr b
with Bind b : Type
  := NonRec : b -> (Expr b) -> Bind b
  |  Rec : list (b * (Expr b))%type -> Bind b
where "'Arg'" := (GHC.Base.Synonym Arg__raw Expr%type)
and   "'Alt'" := (GHC.Base.Synonym Alt__raw (fun b_ =>
                                      (AltCon * list b_ * Expr b_)%type%type)).

Definition CoreAlt :=
  (Alt CoreBndr)%type.

Definition InAlt :=
  CoreAlt%type.

Definition OutAlt :=
  CoreAlt%type.

Definition CoreArg :=
  (Arg CoreBndr)%type.

Definition InArg :=
  CoreArg%type.

Definition OutArg :=
  CoreArg%type.

Definition TaggedArg t :=
  (Arg (TaggedBndr t))%type.

Definition CoreBind :=
  (Bind CoreBndr)%type.

Definition CoreProgram :=
  (list CoreBind)%type.

Definition InBind :=
  CoreBind%type.

Definition OutBind :=
  CoreBind%type.

Definition TaggedBind t :=
  (Bind (TaggedBndr t))%type.

Definition CoreExpr :=
  (Expr CoreBndr)%type.

Inductive CoreVect : Type
  := Vect : Var.Id -> CoreExpr -> CoreVect
  |  NoVect : Var.Id -> CoreVect
  |  VectType : bool -> TyCon.TyCon -> (option TyCon.TyCon) -> CoreVect
  |  VectClass : TyCon.TyCon -> CoreVect
  |  VectInst : Var.Id -> CoreVect.

Definition InExpr :=
  CoreExpr%type.

Definition OutExpr :=
  CoreExpr%type.

Inductive Unfolding : Type
  := NoUnfolding : Unfolding
  |  BootUnfolding : Unfolding
  |  OtherCon : list AltCon -> Unfolding
  |  DFunUnfolding : list Var.Var -> DataCon.DataCon -> list CoreExpr -> Unfolding
  |  CoreUnfolding
   : CoreExpr ->
     UnfoldingSource ->
     bool -> bool -> bool -> bool -> bool -> UnfoldingGuidance -> Unfolding.

Definition IdUnfoldingFun :=
  (Var.Id -> Unfolding)%type.

Definition InScopeEnv :=
  (VarEnv.InScopeSet * IdUnfoldingFun)%type%type.

Definition RuleFun :=
  (DynFlags.DynFlags ->
   InScopeEnv -> Var.Id -> list CoreExpr -> option CoreExpr)%type.

Inductive CoreRule : Type
  := Rule
   : BasicTypes.RuleName ->
     BasicTypes.Activation ->
     Name.Name ->
     list (option Name.Name) ->
     list CoreBndr ->
     list CoreExpr ->
     CoreExpr -> bool -> Module.Module -> IsOrphan -> bool -> CoreRule
  |  BuiltinRule
   : BasicTypes.RuleName -> Name.Name -> GHC.Num.Int -> RuleFun -> CoreRule.

Definition RuleBase :=
  (NameEnv.NameEnv (list CoreRule))%type.

Inductive RuleEnv : Type
  := Mk_RuleEnv : RuleBase -> Module.ModuleSet -> RuleEnv.

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

Instance Default__UnfoldingSource : GHC.Err.Default UnfoldingSource :=
  GHC.Err.Build_Default _ InlineRhs.

Instance Default__UnfoldingGuidance : GHC.Err.Default UnfoldingGuidance :=
  GHC.Err.Build_Default _ UnfNever.

Instance Default__TickishScoping : GHC.Err.Default TickishScoping :=
  GHC.Err.Build_Default _ NoScope.

Instance Default__TickishPlacement : GHC.Err.Default TickishPlacement :=
  GHC.Err.Build_Default _ PlaceRuntime.

Instance Default__IsOrphan : GHC.Err.Default IsOrphan :=
  GHC.Err.Build_Default _ Mk_IsOrphan.

Instance Default__AltCon : GHC.Err.Default AltCon :=
  GHC.Err.Build_Default _ DEFAULT.

Instance Default__Unfolding : GHC.Err.Default Unfolding :=
  GHC.Err.Build_Default _ NoUnfolding.

Definition ug_args (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_args' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs ug_args _ _ => ug_args
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_args' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_arity (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen ug_arity _ _ => ug_arity
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_arity' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_arity' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_boring_ok (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ ug_boring_ok => ug_boring_ok
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_res (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_res' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs _ _ ug_res => ug_res
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_res' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_size (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_size' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs _ ug_size _ => ug_size
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_size' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_unsat_ok (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ ug_unsat_ok _ => ug_unsat_ok
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition df_args (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_args' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_args' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_args' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ _ df_args => df_args
  | CoreUnfolding _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_args' has no match in constructor `CoreUnfolding' of type `Unfolding'")
  end.

Definition df_bndrs (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_bndrs' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_bndrs' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_bndrs' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding df_bndrs _ _ => df_bndrs
  | CoreUnfolding _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_bndrs' has no match in constructor `CoreUnfolding' of type `Unfolding'")
  end.

Definition df_con (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_con' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_con' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_con' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ df_con _ => df_con
  | CoreUnfolding _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `df_con' has no match in constructor `CoreUnfolding' of type `Unfolding'")
  end.

Definition uf_expandable (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_expandable' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_expandable' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_expandable' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_expandable' has no match in constructor `DFunUnfolding' of type `Unfolding'")
  | CoreUnfolding _ _ _ _ _ _ uf_expandable _ => uf_expandable
  end.

Definition uf_guidance (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_guidance' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_guidance' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_guidance' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_guidance' has no match in constructor `DFunUnfolding' of type `Unfolding'")
  | CoreUnfolding _ _ _ _ _ _ _ uf_guidance => uf_guidance
  end.

Definition uf_is_conlike (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_conlike' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_conlike' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_conlike' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_conlike' has no match in constructor `DFunUnfolding' of type `Unfolding'")
  | CoreUnfolding _ _ _ _ uf_is_conlike _ _ _ => uf_is_conlike
  end.

Definition uf_is_top (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_top' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_top' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_top' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_top' has no match in constructor `DFunUnfolding' of type `Unfolding'")
  | CoreUnfolding _ _ uf_is_top _ _ _ _ _ => uf_is_top
  end.

Definition uf_is_value (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_value' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_value' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_value' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_value' has no match in constructor `DFunUnfolding' of type `Unfolding'")
  | CoreUnfolding _ _ _ uf_is_value _ _ _ _ => uf_is_value
  end.

Definition uf_is_work_free (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_work_free' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_work_free' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_work_free' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_is_work_free' has no match in constructor `DFunUnfolding' of type `Unfolding'")
  | CoreUnfolding _ _ _ _ _ uf_is_work_free _ _ => uf_is_work_free
  end.

Definition uf_src (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_src' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_src' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_src' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_src' has no match in constructor `DFunUnfolding' of type `Unfolding'")
  | CoreUnfolding _ uf_src _ _ _ _ _ _ => uf_src
  end.

Definition uf_tmpl (arg_0__ : Unfolding) :=
  match arg_0__ with
  | NoUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_tmpl' has no match in constructor `NoUnfolding' of type `Unfolding'")
  | BootUnfolding =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_tmpl' has no match in constructor `BootUnfolding' of type `Unfolding'")
  | OtherCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_tmpl' has no match in constructor `OtherCon' of type `Unfolding'")
  | DFunUnfolding _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `uf_tmpl' has no match in constructor `DFunUnfolding' of type `Unfolding'")
  | CoreUnfolding uf_tmpl _ _ _ _ _ _ _ => uf_tmpl
  end.

Definition ru_act (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ ru_act _ _ _ _ _ _ _ _ _ => ru_act
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_act' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_args (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ ru_args _ _ _ _ _ => ru_args
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_args' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_auto (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ ru_auto _ _ _ => ru_auto
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_auto' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_bndrs (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ ru_bndrs _ _ _ _ _ _ => ru_bndrs
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_bndrs' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_fn (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ ru_fn _ _ _ _ _ _ _ _ => ru_fn
  | BuiltinRule _ ru_fn _ _ => ru_fn
  end.

Definition ru_local (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ ru_local => ru_local
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_local' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_name (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule ru_name _ _ _ _ _ _ _ _ _ _ => ru_name
  | BuiltinRule ru_name _ _ _ => ru_name
  end.

Definition ru_nargs (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_nargs' has no match in constructor `Rule' of type `CoreRule'")
  | BuiltinRule _ _ ru_nargs _ => ru_nargs
  end.

Definition ru_origin (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ ru_origin _ _ => ru_origin
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_origin' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_orphan (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ ru_orphan _ => ru_orphan
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_orphan' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_rhs (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ ru_rhs _ _ _ _ => ru_rhs
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_rhs' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_rough (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ ru_rough _ _ _ _ _ _ _ => ru_rough
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_rough' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_try (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_try' has no match in constructor `Rule' of type `CoreRule'")
  | BuiltinRule _ _ _ ru_try => ru_try
  end.

Definition re_base (arg_0__ : RuleEnv) :=
  let 'Mk_RuleEnv re_base _ := arg_0__ in
  re_base.

Definition re_visible_orphs (arg_0__ : RuleEnv) :=
  let 'Mk_RuleEnv _ re_visible_orphs := arg_0__ in
  re_visible_orphs.
(* Midamble *)

Parameter tickishCounts : forall {id}, Tickish id -> bool.
Parameter tickishIsCode : forall {id}, Tickish id -> bool.




Fixpoint deAnnotate' {bndr} {annot} (arg_0__ : AnnExpr' bndr annot) : Expr bndr :=
  let deAnnotate {bndr} {annot} : AnnExpr bndr annot -> Expr bndr :=
       fun arg_0__ =>  match arg_0__ with | pair _ e => deAnnotate' e end in
  let deAnnAlt {bndr} {annot} : AnnAlt bndr annot -> Alt bndr :=
      fun arg_0__ =>
        match arg_0__ with
        | pair (pair con args) rhs => pair (pair con args) (deAnnotate rhs)
        end in
    match arg_0__ with
      | AnnType t => Type_ t
      | AnnCoercion co => Coercion co
      | AnnVar v => Var v
      | AnnLit lit => Lit lit
      | AnnLam binder body => Lam binder (deAnnotate body)
      | AnnApp fun_ arg => App (deAnnotate fun_) (deAnnotate arg)
      | AnnCast e (pair _ co) => Cast (deAnnotate e) co
      | AnnTick tick body => Tick tick (deAnnotate body)
      | AnnLet bind body =>
        let deAnnBind :=
            fun arg_9__ =>
              match arg_9__ with
              | AnnNonRec var rhs => NonRec var (deAnnotate rhs)
              | AnnRec pairs => Rec (let cont_11__ arg_12__ :=
                                        match arg_12__ with
                                        | pair v rhs => cons (pair v (deAnnotate rhs)) nil
                                        end in
                                    Coq.Lists.List.flat_map cont_11__ pairs)
              end in
        Let (deAnnBind bind) (deAnnotate body)
      | AnnCase scrut v t alts => Case (deAnnotate scrut) v t (GHC.Base.map deAnnAlt
                                                                           alts)
    end.


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

Fixpoint collectAnnArgs_go {b}{a}(expr : AnnExpr' b a) g as_ :=
  match expr with
    | AnnApp f a => collectAnnArgs_go (snd f) (fst f) (cons a as_)
    | e          => ((g,e), as_)
  end.

Definition collectAnnArgs {b}{a} :
  AnnExpr b a -> (AnnExpr b a * list (AnnExpr b a))%type :=
  fun expr => collectAnnArgs_go (snd expr) (fst expr) nil.


Fixpoint deTagExpr {t} (arg_0__ : TaggedExpr t) : CoreExpr :=
  let deTagAlt {t} : TaggedAlt t -> CoreAlt :=
  fun arg_0__ =>
    match arg_0__ with
      | pair (pair con bndrs) rhs =>
        pair (pair con (let cont_1__ arg_2__ :=
                            match arg_2__ with
                            | TB b _ => cons b nil
                            end in
                        Coq.Lists.List.flat_map cont_1__ bndrs)) (deTagExpr rhs)
    end in
  let deTagBind {t} : TaggedBind t -> CoreBind :=
      fun arg_0__ =>
        match arg_0__ with
        | NonRec (TB b _) rhs => NonRec b (deTagExpr rhs)
        | Rec prs => Rec (let cont_2__ arg_3__ :=
                             match arg_3__ with
                             | pair (TB b _) rhs => cons (pair b (deTagExpr rhs)) nil
                             end in
                         Coq.Lists.List.flat_map cont_2__ prs)
        end
  in match arg_0__ with
     | Var v => Var v
     | Lit l => Lit l
     | Type_ ty => Type_ ty
     | Coercion co => Coercion co
     | App e1 e2 => App (deTagExpr e1) (deTagExpr e2)
     | Lam (TB b _) e => Lam b (deTagExpr e)
     | Let bind body => Let (deTagBind bind) (deTagExpr body)
     | Case e (TB b _) ty alts => Case (deTagExpr e) b ty (GHC.Base.map deTagAlt
                                                                       alts)
     | Tick t e => Tick t (deTagExpr e)
     | Cast e co => Cast (deTagExpr e) co
     end.

Definition exprToType : CoreExpr -> Core.Type_ :=
  fun arg_0__ =>
    match arg_0__ with
      | Type_ ty => ty
      | _bad => GHC.Err.error (GHC.Base.hs_string__ "exprToType")
    end.

Definition applyTypeToArg : Core.Type_ -> (CoreExpr -> Core.Type_) :=
  fun fun_ty arg => TyCoRep.piResultTy fun_ty (exprToType arg).

Instance Default__Expr {b} : GHC.Err.Default (Expr b).
Admitted.

(* Converted value declarations: *)

(* Skipping instance Outputable__TaggedBndr of class Outputable *)

(* Skipping instance Binary__IsOrphan of class Binary *)

Local Definition Ord__AltCon_compare : AltCon -> AltCon -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DataAlt con1, DataAlt con2 =>
        if andb Util.debugIsOn (negb (DataCon.dataConTyCon con1 GHC.Base.==
                                      DataCon.dataConTyCon con2)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreSyn.hs")
              #319)
        else GHC.Base.compare (DataCon.dataConTag con1) (DataCon.dataConTag con2)
    | DataAlt _, _ => Gt
    | _, DataAlt _ => Lt
    | LitAlt l1, LitAlt l2 => GHC.Base.compare l1 l2
    | LitAlt _, DEFAULT => Gt
    | DEFAULT, DEFAULT => Eq
    | DEFAULT, _ => Lt
    end.

Local Definition Ord__AltCon_op_zg__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base.== Gt.

Local Definition Ord__AltCon_op_zgze__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base./= Lt.

Local Definition Ord__AltCon_op_zl__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base.== Lt.

Local Definition Ord__AltCon_op_zlze__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base./= Gt.

Local Definition Ord__AltCon_max : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then y else x.

Local Definition Ord__AltCon_min : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then x else y.

(* Skipping instance Outputable__AltCon of class Outputable *)

Local Definition Eq___UnfoldingGuidance_op_zeze__
   : UnfoldingGuidance -> UnfoldingGuidance -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UnfWhen a1 a2 a3, UnfWhen b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | UnfIfGoodArgs a1 a2 a3, UnfIfGoodArgs b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | UnfNever, UnfNever => true
    | _, _ => false
    end.

Local Definition Eq___UnfoldingGuidance_op_zsze__
   : UnfoldingGuidance -> UnfoldingGuidance -> bool :=
  fun x y => negb (Eq___UnfoldingGuidance_op_zeze__ x y).

Program Instance Eq___UnfoldingGuidance : GHC.Base.Eq_ UnfoldingGuidance :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___UnfoldingGuidance_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___UnfoldingGuidance_op_zsze__ |}.

(* Skipping instance Data__IsOrphan of class Data *)

Local Definition Eq___TickishPlacement_op_zeze__
   : TickishPlacement -> TickishPlacement -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | PlaceRuntime, PlaceRuntime => true
    | PlaceNonLam, PlaceNonLam => true
    | PlaceCostCentre, PlaceCostCentre => true
    | _, _ => false
    end.

Local Definition Eq___TickishPlacement_op_zsze__
   : TickishPlacement -> TickishPlacement -> bool :=
  fun x y => negb (Eq___TickishPlacement_op_zeze__ x y).

Program Instance Eq___TickishPlacement : GHC.Base.Eq_ TickishPlacement :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TickishPlacement_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TickishPlacement_op_zsze__ |}.

Local Definition Eq___TickishScoping_op_zeze__
   : TickishScoping -> TickishScoping -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoScope, NoScope => true
    | SoftScope, SoftScope => true
    | CostCentreScope, CostCentreScope => true
    | _, _ => false
    end.

Local Definition Eq___TickishScoping_op_zsze__
   : TickishScoping -> TickishScoping -> bool :=
  fun x y => negb (Eq___TickishScoping_op_zeze__ x y).

Program Instance Eq___TickishScoping : GHC.Base.Eq_ TickishScoping :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TickishScoping_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TickishScoping_op_zsze__ |}.

(* Skipping instance Data__Bind of class Data *)

(* Skipping instance Data__Expr of class Data *)

(* Skipping instance Data__Tickish of class Data *)

(* Translating `instance Ord__Tickish' failed: using a record pattern for the
   unknown constructor `ProfNote' unsupported *)

Local Definition Eq___Tickish_op_zsze__ {inst_id} `{_ : GHC.Base.Eq_ inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => false.

Local Definition Eq___Tickish_op_zeze__ {inst_id} `{_ : GHC.Base.Eq_ inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => true.

Program Instance Eq___Tickish {id} `{GHC.Base.Eq_ id}
   : GHC.Base.Eq_ (Tickish id) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Tickish_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Tickish_op_zsze__ |}.

(* Skipping instance Data__AltCon of class Data *)

Local Definition Eq___AltCon_op_zeze__ : AltCon -> AltCon -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DataAlt a1, DataAlt b1 => ((a1 GHC.Base.== b1))
    | LitAlt a1, LitAlt b1 => ((a1 GHC.Base.== b1))
    | DEFAULT, DEFAULT => true
    | _, _ => false
    end.

Local Definition Eq___AltCon_op_zsze__ : AltCon -> AltCon -> bool :=
  fun x y => negb (Eq___AltCon_op_zeze__ x y).

Program Instance Eq___AltCon : GHC.Base.Eq_ AltCon :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___AltCon_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___AltCon_op_zsze__ |}.

Program Instance Ord__AltCon : GHC.Base.Ord AltCon :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__AltCon_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__AltCon_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__AltCon_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__AltCon_op_zgze__ ;
         GHC.Base.compare__ := Ord__AltCon_compare ;
         GHC.Base.max__ := Ord__AltCon_max ;
         GHC.Base.min__ := Ord__AltCon_min |}.

Definition bindersOf {b} : Bind b -> list b :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec binder _ => cons binder nil
    | Rec pairs =>
        let cont_2__ arg_3__ := let 'pair binder _ := arg_3__ in cons binder nil in
        Coq.Lists.List.flat_map cont_2__ pairs
    end.

Definition bindersOfBinds {b} : list (Bind b) -> list b :=
  fun binds =>
    Data.Foldable.foldr (Coq.Init.Datatypes.app GHC.Base.∘ bindersOf) nil binds.

Definition bootUnfolding : Unfolding :=
  BootUnfolding.

Definition boringCxtNotOk : bool :=
  false.

Definition boringCxtOk : bool :=
  true.

Definition chooseOrphanAnchor (local_names : list Name.Name) : IsOrphan :=
  match GHC.Base.map Name.nameOccName local_names with
  | cons hd tl => NotOrphan (Data.Foldable.foldr GHC.Base.min hd tl)
  | nil => Mk_IsOrphan
  end.

Definition cmpAltCon : AltCon -> AltCon -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DEFAULT, DEFAULT => Eq
    | DEFAULT, _ => Lt
    | DataAlt d1, DataAlt d2 =>
        GHC.Base.compare (DataCon.dataConTag d1) (DataCon.dataConTag d2)
    | DataAlt _, DEFAULT => Gt
    | LitAlt l1, LitAlt l2 => GHC.Base.compare l1 l2
    | LitAlt _, DEFAULT => Gt
    | con1, con2 =>
        Panic.warnPprTrace (true) (GHC.Base.hs_string__
                            "ghc/compiler/coreSyn/CoreSyn.hs") #1700 (GHC.Base.mappend (GHC.Base.mappend (id
                                                                                                          (GHC.Base.hs_string__
                                                                                                           "Comparing incomparable AltCons"))
                                                                                                         (Panic.noString
                                                                                                          con1))
                                                                                       (Panic.noString con2)) Lt
    end.

Definition cmpAlt {a} {b}
   : (AltCon * a * b)%type -> (AltCon * a * b)%type -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair (pair con1 _) _, pair (pair con2 _) _ => cmpAltCon con1 con2
    end.

Definition ltAlt {a} {b}
   : (AltCon * a * b)%type -> (AltCon * a * b)%type -> bool :=
  fun a1 a2 => (cmpAlt a1 a2) GHC.Base.== Lt.

Definition collectAnnArgsTicks {b} {a}
   : (Tickish Var.Var -> bool) ->
     AnnExpr b a ->
     (AnnExpr b a * list (AnnExpr b a) * list (Tickish Var.Var))%type :=
  fun tickishOk expr =>
    let go :=
      GHC.DeferredFix.deferredFix3 (fun go arg_0__ arg_1__ arg_2__ =>
                                      let j_4__ :=
                                        match arg_0__, arg_1__, arg_2__ with
                                        | e, as_, ts => pair (pair e as_) (GHC.List.reverse ts)
                                        end in
                                      match arg_0__, arg_1__, arg_2__ with
                                      | pair _ (AnnApp f a), as_, ts => go f (cons a as_) ts
                                      | pair _ (AnnTick t e), as_, ts =>
                                          if tickishOk t : bool then go e as_ (cons t ts) else
                                          j_4__
                                      | _, _, _ => j_4__
                                      end) in
    go expr nil nil.

Definition collectAnnBndrs {bndr} {annot}
   : AnnExpr bndr annot -> (list bndr * AnnExpr bndr annot)%type :=
  fun e =>
    let collect :=
      GHC.DeferredFix.deferredFix2 (fun collect arg_0__ arg_1__ =>
                                      match arg_0__, arg_1__ with
                                      | bs, pair _ (AnnLam b body) => collect (cons b bs) body
                                      | bs, body => pair (GHC.List.reverse bs) body
                                      end) in
    collect nil e.

Definition collectArgs {b} : Expr b -> (Expr b * list (Arg b))%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | App f a, as_ => go f (cons a as_)
                 | e, as_ => pair e as_
                 end in
    go expr nil.

Definition collectArgsTicks {b}
   : (Tickish Var.Id -> bool) ->
     Expr b -> (Expr b * list (Arg b) * list (Tickish Var.Id))%type :=
  fun skipTick expr =>
    let fix go arg_0__ arg_1__ arg_2__
              := let j_4__ :=
                   match arg_0__, arg_1__, arg_2__ with
                   | e, as_, ts => pair (pair e as_) (GHC.List.reverse ts)
                   end in
                 match arg_0__, arg_1__, arg_2__ with
                 | App f a, as_, ts => go f (cons a as_) ts
                 | Tick t e, as_, ts => if skipTick t : bool then go e as_ (cons t ts) else j_4__
                 | _, _, _ => j_4__
                 end in
    go expr nil nil.

Definition collectBinders {b} : Expr b -> (list b * Expr b)%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | bs, Lam b e => go (cons b bs) e
                 | bs, e => pair (GHC.List.reverse bs) e
                 end in
    go nil expr.

Definition collectNAnnBndrs {bndr} {annot}
   : GHC.Num.Int -> AnnExpr bndr annot -> (list bndr * AnnExpr bndr annot)%type :=
  fun orig_n e =>
    let fix collect arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | num_3__, bs, body =>
                     if num_3__ GHC.Base.== #0 : bool then pair (GHC.List.reverse bs) body else
                     match arg_0__, arg_1__, arg_2__ with
                     | n, bs, pair _ (AnnLam b body) => collect (n GHC.Num.- #1) (cons b bs) body
                     | _, _, _ =>
                         Panic.panicStr (GHC.Base.hs_string__ "collectNBinders") (Panic.noString orig_n)
                     end
                 end in
    collect orig_n nil e.

Definition collectNBinders {b}
   : GHC.Num.Int -> Expr b -> (list b * Expr b)%type :=
  fun orig_n orig_expr =>
    let fix go arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | num_3__, bs, expr =>
                     if num_3__ GHC.Base.== #0 : bool then pair (GHC.List.reverse bs) expr else
                     match arg_0__, arg_1__, arg_2__ with
                     | n, bs, Lam b e => go (n GHC.Num.- #1) (cons b bs) e
                     | _, _, _ =>
                         Panic.panicStr (GHC.Base.hs_string__ "collectNBinders") (Panic.noString orig_n)
                     end
                 end in
    go orig_n nil orig_expr.

Definition collectTyBinders : CoreExpr -> (list Var.TyVar * CoreExpr)%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__, arg_1__ with
                   | tvs, e => pair (GHC.List.reverse tvs) e
                   end in
                 match arg_0__, arg_1__ with
                 | tvs, Lam b e => if Var.isTyVar b : bool then go (cons b tvs) e else j_3__
                 | _, _ => j_3__
                 end in
    go nil expr.

Definition collectValBinders : CoreExpr -> (list Var.Id * CoreExpr)%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__, arg_1__ with
                   | ids, body => pair (GHC.List.reverse ids) body
                   end in
                 match arg_0__, arg_1__ with
                 | ids, Lam b e => if Var.isId b : bool then go (cons b ids) e else j_3__
                 | _, _ => j_3__
                 end in
    go nil expr.

Definition collectTyAndValBinders
   : CoreExpr -> (list Var.TyVar * list Var.Id * CoreExpr)%type :=
  fun expr =>
    let 'pair tvs body1 := collectTyBinders expr in
    let 'pair ids body := collectValBinders body1 in
    pair (pair tvs ids) body.

Definition deAnnotate {bndr} {annot} : AnnExpr bndr annot -> Expr bndr :=
  fun arg_0__ => let 'pair _ e := arg_0__ in deAnnotate' e.

Definition deAnnBind {b} {annot} : AnnBind b annot -> Bind b :=
  fun arg_0__ =>
    match arg_0__ with
    | AnnNonRec var rhs => NonRec var (deAnnotate rhs)
    | AnnRec pairs =>
        Rec (let cont_2__ arg_3__ :=
               let 'pair v rhs := arg_3__ in
               cons (pair v (deAnnotate rhs)) nil in
             Coq.Lists.List.flat_map cont_2__ pairs)
    end.

Definition deAnnAlt {bndr} {annot} : AnnAlt bndr annot -> Alt bndr :=
  fun arg_0__ =>
    let 'pair (pair con args) rhs := arg_0__ in
    pair (pair con args) (deAnnotate rhs).

Definition deTagAlt {t} : TaggedAlt t -> CoreAlt :=
  fun arg_0__ =>
    let 'pair (pair con bndrs) rhs := arg_0__ in
    pair (pair con (let cont_1__ arg_2__ := let 'TB b _ := arg_2__ in cons b nil in
                Coq.Lists.List.flat_map cont_1__ bndrs)) (deTagExpr rhs).

Definition deTagBind {t} : TaggedBind t -> CoreBind :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec (TB b _) rhs => NonRec b (deTagExpr rhs)
    | Rec prs =>
        Rec (let cont_2__ arg_3__ :=
               let 'pair (TB b _) rhs := arg_3__ in
               cons (pair b (deTagExpr rhs)) nil in
             Coq.Lists.List.flat_map cont_2__ prs)
    end.

Definition emptyRuleEnv : RuleEnv :=
  Mk_RuleEnv NameEnv.emptyNameEnv Module.emptyModuleSet.

Definition evaldUnfolding : Unfolding :=
  OtherCon nil.

Definition expandUnfolding_maybe : Unfolding -> option CoreExpr :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreUnfolding rhs _ _ _ _ _ true _ => Some rhs
    | _ => None
    end.

Definition exprToCoercion_maybe : CoreExpr -> option unit :=
  fun arg_0__ => match arg_0__ with | Coercion co => Some co | _ => None end.

Definition flattenBinds {b} : list (Bind b) -> list (b * Expr b)%type :=
  fix flattenBinds arg_0__
        := match arg_0__ with
           | cons (NonRec b r) binds => cons (pair b r) (flattenBinds binds)
           | cons (Rec prs1) binds => Coq.Init.Datatypes.app prs1 (flattenBinds binds)
           | nil => nil
           end.

Definition hasSomeUnfolding : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | NoUnfolding => false
    | BootUnfolding => false
    | _ => true
    end.

Definition isAutoRule : CoreRule -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => false
    | Rule _ _ _ _ _ _ _ is_auto _ _ _ => is_auto
    end.

Definition isBootUnfolding : Unfolding -> bool :=
  fun arg_0__ => match arg_0__ with | BootUnfolding => true | _ => false end.

Definition isBuiltinRule : CoreRule -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => true
    | _ => false
    end.

Definition isCheapUnfolding : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreUnfolding _ _ _ _ _ is_wf _ _ => is_wf
    | _ => false
    end.

Definition isCompulsoryUnfolding : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreUnfolding _ InlineCompulsory _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isConLikeUnfolding : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | OtherCon _ => true
    | CoreUnfolding _ _ _ _ con _ _ _ => con
    | _ => false
    end.

Definition isEvaldUnfolding : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | OtherCon _ => true
    | CoreUnfolding _ _ _ is_evald _ _ _ _ => is_evald
    | _ => false
    end.

Definition isExpandableUnfolding : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreUnfolding _ _ _ _ _ _ is_expable _ => is_expable
    | _ => false
    end.

Definition isFragileUnfolding : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreUnfolding _ _ _ _ _ _ _ _ => true
    | DFunUnfolding _ _ _ => true
    | _ => false
    end.

Definition isLocalRule : CoreRule -> bool :=
  ru_local.

Definition isOrphan : IsOrphan -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_IsOrphan => true | _ => false end.

Definition isRuntimeVar : Var.Var -> bool :=
  Var.isId.

Definition isStableSource : UnfoldingSource -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | InlineCompulsory => true
    | InlineStable => true
    | InlineRhs => false
    end.

Definition isStableUnfolding : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreUnfolding _ src _ _ _ _ _ _ => isStableSource src
    | DFunUnfolding _ _ _ => true
    | _ => false
    end.

Definition isTyCoArg {b} : Expr b -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Type_ _ => true
    | Coercion _ => true
    | _ => false
    end.

Definition isTypeArg {b} : Expr b -> bool :=
  fun arg_0__ => match arg_0__ with | Type_ _ => true | _ => false end.

Definition isValArg {b} : Expr b -> bool :=
  fun e => negb (isTypeArg e).

Definition valArgCount {b} : list (Arg b) -> GHC.Num.Int :=
  Util.count isValArg.

Definition isRuntimeArg : CoreExpr -> bool :=
  isValArg.

Definition isValueUnfolding : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreUnfolding _ _ _ is_evald _ _ _ _ => is_evald
    | _ => false
    end.

Definition mkApps {b} : Expr b -> list (Arg b) -> Expr b :=
  fun f args => Data.Foldable.foldl App f args.

Definition mkConApp {b} : DataCon.DataCon -> list (Arg b) -> Expr b :=
  fun con args => mkApps (Var (DataCon.dataConWorkId con)) args.

Definition mkCharLit {b} : GHC.Char.Char -> Expr b :=
  fun c => Lit (Literal.mkMachChar c).

Definition mkCoApps {b} : Expr b -> list unit -> Expr b :=
  fun f args => Data.Foldable.foldl (fun e a => App e (Coercion a)) f args.

Definition mkCoBind : Var.CoVar -> unit -> CoreBind :=
  fun cv co => NonRec cv (Coercion co).

Definition mkDoubleLit {b} : GHC.Real.Rational -> Expr b :=
  fun d => Lit (Literal.mkMachDouble d).

Definition mkFloatLit {b} : GHC.Real.Rational -> Expr b :=
  fun f => Lit (Literal.mkMachFloat f).

Definition mkLams {b} : list b -> Expr b -> Expr b :=
  fun binders body => Data.Foldable.foldr Lam body binders.

Definition maybeUnfoldingTemplate : Unfolding -> option CoreExpr :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreUnfolding expr _ _ _ _ _ _ _ => Some expr
    | DFunUnfolding bndrs con args =>
        Some (mkLams bndrs (mkApps (Var (DataCon.dataConWorkId con)) args))
    | _ => None
    end.

Definition mkLet {b} : Bind b -> Expr b -> Expr b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Rec nil, body => body
    | bind, body => Let bind body
    end.

Definition mkLets {b} : list (Bind b) -> Expr b -> Expr b :=
  fun binds body => Data.Foldable.foldr mkLet body binds.

Definition mkLetNonRec {b} : b -> Expr b -> Expr b -> Expr b :=
  fun b rhs body => Let (NonRec b rhs) body.

Definition mkLetRec {b} : list (b * Expr b)%type -> Expr b -> Expr b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, body => body
    | bs, body => Let (Rec bs) body
    end.

Definition mkOtherCon : list AltCon -> Unfolding :=
  OtherCon.

Definition mkRuleEnv : RuleBase -> list Module.Module -> RuleEnv :=
  fun rules vis_orphs => Mk_RuleEnv rules (Module.mkModuleSet vis_orphs).

Definition mkStringLit {b} : GHC.Base.String -> Expr b :=
  fun s => Lit (Literal.mkMachString s).

Definition mkTyArg {b} : unit -> Expr b :=
  fun ty =>
    match TyCoRep.Type_isCoercionTy_maybe ty with
    | Some co => Coercion co
    | _ => Type_ ty
    end.

Definition mkTyApps {b} : Expr b -> list unit -> Expr b :=
  fun f args => Data.Foldable.foldl (fun e a => App e (mkTyArg a)) f args.

Definition mkTyBind : Var.TyVar -> unit -> CoreBind :=
  fun tv ty => NonRec tv (Type_ ty).

Definition needSaturated : bool :=
  false.

Definition neverUnfoldGuidance : UnfoldingGuidance -> bool :=
  fun arg_0__ => match arg_0__ with | UnfNever => true | _ => false end.

Definition canUnfold : Unfolding -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreUnfolding _ _ _ _ _ _ _ g => negb (neverUnfoldGuidance g)
    | _ => false
    end.

Definition noUnfolding : Unfolding :=
  NoUnfolding.

Definition notOrphan : IsOrphan -> bool :=
  fun arg_0__ => match arg_0__ with | NotOrphan _ => true | _ => false end.

Definition otherCons : Unfolding -> list AltCon :=
  fun arg_0__ => match arg_0__ with | OtherCon cons_ => cons_ | _ => nil end.

Definition rhssOfAlts {b} : list (Alt b) -> list (Expr b) :=
  fun alts =>
    let cont_0__ arg_1__ := let 'pair (pair _ _) e := arg_1__ in cons e nil in
    Coq.Lists.List.flat_map cont_0__ alts.

Definition rhssOfBind {b} : Bind b -> list (Expr b) :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec _ rhs => cons rhs nil
    | Rec pairs =>
        let cont_2__ arg_3__ := let 'pair _ rhs := arg_3__ in cons rhs nil in
        Coq.Lists.List.flat_map cont_2__ pairs
    end.

Definition ruleActivation : CoreRule -> BasicTypes.Activation :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => BasicTypes.AlwaysActive
    | Rule _ act _ _ _ _ _ _ _ _ _ => act
    end.

Definition ruleArity : CoreRule -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ n _ => n
    | Rule _ _ _ _ _ args _ _ _ _ _ => Data.Foldable.length args
    end.

Definition ruleIdName : CoreRule -> Name.Name :=
  ru_fn.

Definition ruleModule : CoreRule -> option Module.Module :=
  fun arg_0__ =>
    match arg_0__ with
    | Rule _ _ _ _ _ _ _ _ ru_origin _ _ => Some ru_origin
    | BuiltinRule _ _ _ _ => None
    end.

Definition ruleName : CoreRule -> BasicTypes.RuleName :=
  ru_name.

Definition setRuleIdName : Name.Name -> CoreRule -> CoreRule :=
  fun nm ru =>
    match ru with
    | Rule ru_name_0__ ru_act_1__ ru_fn_2__ ru_rough_3__ ru_bndrs_4__ ru_args_5__
    ru_rhs_6__ ru_auto_7__ ru_origin_8__ ru_orphan_9__ ru_local_10__ =>
        Rule ru_name_0__ ru_act_1__ nm ru_rough_3__ ru_bndrs_4__ ru_args_5__ ru_rhs_6__
             ru_auto_7__ ru_origin_8__ ru_orphan_9__ ru_local_10__
    | BuiltinRule ru_name_11__ ru_fn_12__ ru_nargs_13__ ru_try_14__ =>
        BuiltinRule ru_name_11__ nm ru_nargs_13__ ru_try_14__
    end.

Axiom tickishPlace : forall {A : Type}, A.

(* Translating `tickishPlace' failed: using a record pattern for the unknown
   constructor `ProfNote' unsupported *)

Axiom tickishScoped : forall {A : Type}, A.

(* Translating `tickishScoped' failed: using a record pattern for the unknown
   constructor `ProfNote' unsupported *)

Definition unSaturatedOk : bool :=
  true.

Definition unfoldingTemplate : Unfolding -> CoreExpr :=
  uf_tmpl.

Definition valBndrCount : list CoreBndr -> GHC.Num.Int :=
  Util.count Var.isId.

Definition varToCoreExpr {b} : CoreBndr -> Expr b :=
  fun v =>
    if Var.isTyVar v : bool then Type_ (TyCoRep.mkTyVarTy v) else
    if Var.isCoVar v : bool then Coercion (TyCoRep.mkCoVarCo v) else
    if andb Util.debugIsOn (negb (Var.isId v)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreSyn.hs")
          #1920)
    else Var v.

Definition varsToCoreExprs {b} : list CoreBndr -> list (Expr b) :=
  fun vs => GHC.Base.map varToCoreExpr vs.

Definition mkVarApps {b} : Expr b -> list Var.Var -> Expr b :=
  fun f vars => Data.Foldable.foldl (fun e a => App e (varToCoreExpr a)) f vars.

Definition mkConApp2 {b}
   : DataCon.DataCon -> list unit -> list Var.Var -> Expr b :=
  fun con tys arg_ids =>
    mkApps (mkApps (Var (DataCon.dataConWorkId con)) (GHC.Base.map Type_ tys))
           (GHC.Base.map varToCoreExpr arg_ids).

(* External variables:
     Alt AnnAlt AnnExpr Arg Eq Gt Lt None Some Type andb bool comparison cons
     deAnnotate' deTagExpr false id list negb nil op_zt__ option pair true unit
     BasicTypes.Activation BasicTypes.AlwaysActive BasicTypes.Arity
     BasicTypes.RuleName Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Data.Foldable.foldl Data.Foldable.foldr Data.Foldable.length DataCon.DataCon
     DataCon.dataConTag DataCon.dataConTyCon DataCon.dataConWorkId DynFlags.DynFlags
     GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String GHC.Base.Synonym GHC.Base.compare
     GHC.Base.compare__ GHC.Base.map GHC.Base.mappend GHC.Base.max__ GHC.Base.min
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zl____ GHC.Base.op_zlze____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Char.Char
     GHC.DeferredFix.deferredFix2 GHC.DeferredFix.deferredFix3 GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.error GHC.List.reverse GHC.Num.Int GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Real.Rational Literal.Literal Literal.mkMachChar
     Literal.mkMachDouble Literal.mkMachFloat Literal.mkMachString Module.Module
     Module.ModuleSet Module.emptyModuleSet Module.mkModuleSet Name.Name
     Name.nameOccName NameEnv.NameEnv NameEnv.emptyNameEnv OccName.OccName
     Panic.assertPanic Panic.noString Panic.panicStr Panic.warnPprTrace
     TyCoRep.Type_isCoercionTy_maybe TyCoRep.mkCoVarCo TyCoRep.mkTyVarTy TyCon.TyCon
     Util.count Util.debugIsOn Var.CoVar Var.Id Var.TyVar Var.Var Var.isCoVar
     Var.isId Var.isTyVar VarEnv.InScopeSet
*)
