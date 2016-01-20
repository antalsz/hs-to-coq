Require Import Ssreflect.ssreflect.
Require Import Ssreflect.eqtype Ssreflect.fintype.
Require Import Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.seq.
Require Import MathComp.ssrint.
Require Import Coq.Strings.String Coq.ZArith.BinInt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Definition Int := Z. (* Does this integrate with SSReflect? *)

Record FastString := MkFastString { fs_value : string }. (* I do *not* want to verify this :-) *)

Parameter DataCon Literal Type_ Coercion : Type.
Parameter CostCentre Module RealSrcSpan : Type.

Hypothesis OccName SrcSpan TyThing : Type.

Inductive BuiltInSyntax : Type := BuiltInSyntax_ | UserSyntax.

Inductive NameSort : Type
  := External of Module
  |  WiredIn  of Module & TyThing & BuiltInSyntax
  |  Internal
  |  System.


Record Name : Type := MkName { n_sort : NameSort
                             ; n_occ  : OccName
                             ; n_uniq : Int
                             ; n_loc  : SrcSpan }.

Inductive ExportFlag : Type := NotExported
                            |  Exported.

Inductive IdScope : Type := GlobalId
                         |  LocalId of ExportFlag.

Hypothesis Kind TcTyVarDetails IdDetails : Type.

Definition Arity : Type := Int.

Definition ArityInfo : Type := Arity.

Definition RuleName : Type := FastString.

Definition PhaseNum : Type := Int.

Inductive CompilerPhase : Type := Phase of PhaseNum
                               |  InitialPhase.

Inductive Activation := NeverActive
                     |  AlwaysActive
                     |  ActiveBefore of PhaseNum
                     |  ActiveAfter  of PhaseNum.

Inductive CoreRule : Type :=
  | Rule (ru_name   : RuleName)
         (ru_act    : Activation)

         (ru_fn     : Name)
         (ru_rough  : seq (option Name))

         (ru_bndrs  : seq CoreBndr)
         (ru_args   : seq CoreExpr)

         (ru_rhs    : CoreExpr)

         (ru_auto   : Bool)

         (ru_origin : Module)

         (ru_orphan : IsOrphan)

         (ru_local  : Bool)

  | BuiltinRule (ru_name  : RuleName)
                (ru_fn    : Name)
                (ru_nargs : Int)
                (ru_try   : RuleFun).

(* type RuleBase = NameEnv [CoreRule] *)
(*         -- The rules are unordered; *)
(*         -- we sort out any overlaps on lookup *)

(* -- | A full rule environment which we can apply rules from.  Like a 'RuleBase', *)
(* -- but it also includes the set of visible orphans we use to filter out orphan *)
(* -- rules which are not visible (even though we can see them...) *)
(* data RuleEnv *)
(*     = RuleEnv { re_base          :: RuleBase *)
(*               , re_visible_orphs :: ModuleSet *)
(*               } *)

(* mkRuleEnv :: RuleBase -> [Module] -> RuleEnv *)
(* mkRuleEnv rules vis_orphs = RuleEnv rules (mkModuleSet vis_orphs) *)

(* emptyRuleEnv :: RuleEnv *)
(* emptyRuleEnv = RuleEnv emptyNameEnv emptyModuleSet *)

(* type RuleFun = DynFlags -> InScopeEnv -> Id -> [CoreExpr] -> Maybe CoreExpr *)
(* type InScopeEnv = (InScopeSet, IdUnfoldingFun) *)

(* type IdUnfoldingFun = Id -> Unfolding *)

Inductive RuleInfo : Type := MkRuleInfo of seq CoreRule & DVarSet.

Record IdInfo := MkIdInfo { arityInfo       : ArityInfo
                          ; ruleInfo        : RuleInfo
                          ; unfoldingInfo   : Unfolding
                          ; cafInfo         : CafInfo
                          ; oneShotInfo     : OneShotInfo
                          ; inlinePragInfo  : InlinePragma
                          ; occInfo         : OccInfo
                          ; strictnessInfo  : StrictSig
                          ; demandInfo      : Demand
                          ; callArityInfo   : ArityInfo }.


Inductive Var : Type :=
  | TyVarV (varName    : Name)
           (realUnique : Int)
           (varType    : Kind)
  | TcTyVarV (varName        : Name)
             (realUnique     : Int)
             (varType        : Kind)
             (tc_tv_details  : TcTyVarDetails)
  | IdV (varName    : Name)
        (realUnique : Int)
        (varType    : Type_)
        (idScope    : IdScope)
        (id_details : IdDetails)
        (id_info    : IdInfo).

Definition Id : Type := Var.

Definition TyVar   : Type := Var.

Definition TKVar   : Type := Var.
Definition TypeVar : Type := Var.
Definition KindVar : Type := Var.

Definition EvId    : Type := Id.
Definition EvVar   : Type := EvId.
Definition DFunId  : Type := Id.
Definition DictId  : Type := EvId.
Definition IpId    : Type := EvId.
Definition EqVar   : Type := EvId.

Definition CoVar : Type := Id.

Definition TyCoVar : Type := Id.

Inductive Tickish (id : Type) : Type :=
  | ProfNote   (profNoteCC : CostCentre) (profNoteCount : bool) (profNoteScope : bool)
  | HpcTick    (tickModule : Module) (tickId : Int)
  | Breakpoint (breakpointId : Int) (breakpointFVs : seq id)
  | SourceNote (sourceSpan : RealSrcSpan) (sourceName : string).

Inductive AltCon : Type :=
  | DataAlt of DataCon
  | LitAlt  of Literal
  | DEFAULT.

Definition ArgRec (Expr : Type -> Type) (b : Type) : Type := Expr b.
Definition AltRec (Expr : Type -> Type) (b : Type) : Type := (AltCon * seq b * Expr b)%type.

Reserved Notation "'Arg'".
Reserved Notation "'Alt'".
Inductive
  Expr (b : Type) : Type :=
    | EVar      of Id
    | ELit      of Literal
    | EApp      of Expr b & Arg b
    | ELam      of b & Expr b
    | ELet      of Bind b & Expr b
    | ECase     of Expr b & b & Type_ & seq (Alt b)
    | ECast     of Expr b & Coercion
    | ETick     of Tickish Id & Expr b
    | EType     of Type_
    | ECoercion of Coercion
with
  Bind (b : Type) : Type :=
    | NonRec of b & Expr b
    | Rec    of seq (b * Expr b)
where "'Arg'" := (ArgRec Expr)
and   "'Alt'" := (AltRec Expr).

Definition CoreBndr    : Type := Var.

Definition CoreExpr    : Type := Expr CoreBndr.
Definition CoreArg     : Type := Arg  CoreBndr.
Definition CoreBind    : Type := Bind CoreBndr.
Definition CoreAlt     : Type := Alt  CoreBndr.

Definition CoreProgram : Type := seq CoreBind.
