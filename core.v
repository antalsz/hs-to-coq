Require Import Ssreflect.ssreflect.
Require Import Ssreflect.eqtype Ssreflect.fintype.
Require Import Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.seq.
Require Import MathComp.ssrint.
Require Import string.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Parameter DataCon Literal Type_ Coercion : Type.
Parameter CostCentre Module RealSrcSpan : Type.

Hypothesis Name Kind TcTyVarDetails IdScope IdDetails IdInfo : Type.
Inductive Var : Type :=
  | TyVarV (varName    : Name)
           (realUnique : int)
           (varType    : Kind)
  | TcTyVarV (varName        : Name)
             (realUnique     : int)
             (varType        : Kind)
             (tc_tv_details  : TcTyVarDetails)
  | IdV (varName    : Name)
        (realUnique : int)
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
  | HpcTick    (tickModule : Module) (tickId : int)
  | Breakpoint (breakpointId : int) (breakpointFVs : seq id)
  | SourceNote (sourceSpan : RealSrcSpan) (sourceName : string).

Inductive AltCon : Type :=
  | DataAlt (c : DataCon)
  | LitAlt  (l : Literal)
  | DEFAULT.

Hypothesis Arg : Type -> Type (* Arg = Expr *).
Inductive
  Expr (b : Type) : Type :=
    | EVar      (v : Id)
    | ELit      (l : Literal)
    | EApp      (e1 : Expr b) (e2 : Arg b)
    | ELam      (x : b) (e : Expr b)
    | ELet      (bind : Bind b) (body : Expr b)
    | ECase     (scrut : Expr b) (bind : b) (res_ty : Type_) (alts : seq (Alt b))
    | ECast     (e : Expr b) (co : Coercion)
    | ETick     (t : Tickish Id) (e : Expr b)
    | EType     (ty : Type_)
    | ECoercion (co : Coercion)
with
  Alt (b : Type) : Type :=
    | MkAlt (c : AltCon) (xs : seq b) (e : Expr b)
with
  Bind (b : Type) : Type :=
    | NonRec (x : b) (e : Expr b)
    | Rec    (binds : seq (b * Expr b)).


Definition CoreBndr    : Type := Var.

Definition CoreExpr    : Type := Expr CoreBndr.
Definition CoreArg     : Type := Arg  CoreBndr.
Definition CoreBind    : Type := Bind CoreBndr.
Definition CoreAlt     : Type := Alt  CoreBndr.

Definition CoreProgram : Type := seq CoreBind.
