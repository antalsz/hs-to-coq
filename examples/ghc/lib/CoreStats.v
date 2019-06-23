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
Require Core.
Require Data.Foldable.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require Id.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive CoreStats : Type
  := | CS (cs_tm : nat) (cs_ty : nat) (cs_co : nat) (cs_vb : nat) (cs_jb : nat)
   : CoreStats.

Instance Default__CoreStats : GHC.Err.Default CoreStats :=
  GHC.Err.Build_Default _ (CS GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default).

Definition cs_co (arg_0__ : CoreStats) :=
  let 'CS _ _ cs_co _ _ := arg_0__ in
  cs_co.

Definition cs_jb (arg_0__ : CoreStats) :=
  let 'CS _ _ _ _ cs_jb := arg_0__ in
  cs_jb.

Definition cs_tm (arg_0__ : CoreStats) :=
  let 'CS cs_tm _ _ _ _ := arg_0__ in
  cs_tm.

Definition cs_ty (arg_0__ : CoreStats) :=
  let 'CS _ cs_ty _ _ _ := arg_0__ in
  cs_ty.

Definition cs_vb (arg_0__ : CoreStats) :=
  let 'CS _ _ _ cs_vb _ := arg_0__ in
  cs_vb.

(* Converted value declarations: *)

Definition zeroCS : CoreStats :=
  CS #0 #0 #0 #0 #0.

Axiom tyStats : unit -> CoreStats.

Definition tickSize : Core.Tickish Core.Id -> nat :=
  fun arg_0__ => match arg_0__ with | Core.ProfNote _ _ _ => #1 | _ => #1 end.

Definition plusCS : CoreStats -> CoreStats -> CoreStats :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CS p1 q1 r1 v1 j1, CS p2 q2 r2 v2 j2 =>
        CS (p1 GHC.Num.+ p2) (q1 GHC.Num.+ q2) (r1 GHC.Num.+ r2) (v1 GHC.Num.+ v2) (j1
            GHC.Num.+
            j2)
    end.

Definition sumCS {a} : (a -> CoreStats) -> list a -> CoreStats :=
  fun f => Data.Foldable.foldl' (fun s a => plusCS s (f a)) zeroCS.

Definition oneTM : CoreStats :=
  let 'CS cs_tm_0__ cs_ty_1__ cs_co_2__ cs_vb_3__ cs_jb_4__ := zeroCS in
  CS #1 cs_ty_1__ cs_co_2__ cs_vb_3__ cs_jb_4__.

Axiom coStats : unit -> CoreStats.

Definition bndrStats : Core.Var -> CoreStats :=
  fun v => plusCS oneTM (tyStats (Core.varType v)).

Definition letBndrStats : BasicTypes.TopLevelFlag -> Core.Var -> CoreStats :=
  fun top_lvl v =>
    let ty_stats := tyStats (Core.varType v) in
    if orb (Core.isTyVar v) (BasicTypes.isTopLevel top_lvl) : bool
    then bndrStats v else
    if Id.isJoinId v : bool
    then plusCS (let 'CS cs_tm_9__ cs_ty_10__ cs_co_11__ cs_vb_12__ cs_jb_13__ :=
                   oneTM in
                 CS cs_tm_9__ cs_ty_10__ cs_co_11__ cs_vb_12__ #1) ty_stats else
    plusCS (let 'CS cs_tm_1__ cs_ty_2__ cs_co_3__ cs_vb_4__ cs_jb_5__ := oneTM in
            CS cs_tm_1__ cs_ty_2__ cs_co_3__ #1 cs_jb_5__) ty_stats.

Definition bndrSize : Core.Var -> nat :=
  fun arg_0__ => #1.

Definition bndrsSize : list Core.Var -> nat :=
  Data.Foldable.sum GHC.Base.∘ GHC.Base.map bndrSize.

Definition exprSize : Core.CoreExpr -> nat :=
  fix exprSize (arg_0__ : Core.CoreExpr) : nat
        := let altSize (arg_0__ : Core.CoreAlt) : nat :=
             let 'pair (pair _ bs) e := arg_0__ in
             bndrsSize bs GHC.Num.+ exprSize e in
           match arg_0__ with
           | Core.Mk_Var _ => #1
           | Core.Lit _ => #1
           | Core.App f a => exprSize f GHC.Num.+ exprSize a
           | Core.Lam b e => bndrSize b GHC.Num.+ exprSize e
           | Core.Let b e => bindSize b GHC.Num.+ exprSize e
           | Core.Case e b _ as_ =>
               ((exprSize e GHC.Num.+ bndrSize b) GHC.Num.+ #1) GHC.Num.+
               Data.Foldable.sum (GHC.Base.map altSize as_)
           | Core.Cast e _ => #1 GHC.Num.+ exprSize e
           | Core.Tick n e => tickSize n GHC.Num.+ exprSize e
           | Core.Type_ _ => #1
           | Core.Coercion _ => #1
           end with bindSize (arg_0__ : Core.CoreBind) : nat
                      := let pairSize (arg_0__ : (Core.Var * Core.CoreExpr)%type) : nat :=
                           let 'pair b e := arg_0__ in
                           bndrSize b GHC.Num.+ exprSize e in
                         match arg_0__ with
                         | Core.NonRec b e => bndrSize b GHC.Num.+ exprSize e
                         | Core.Rec prs => Data.Foldable.sum (GHC.Base.map pairSize prs)
                         end for exprSize.

Definition pairSize : (Core.Var * Core.CoreExpr)%type -> nat :=
  fun '(pair b e) => bndrSize b GHC.Num.+ exprSize e.

Definition bindSize : Core.CoreBind -> nat :=
  fix exprSize (arg_0__ : Core.CoreExpr) : nat
        := let altSize (arg_0__ : Core.CoreAlt) : nat :=
             let 'pair (pair _ bs) e := arg_0__ in
             bndrsSize bs GHC.Num.+ exprSize e in
           match arg_0__ with
           | Core.Mk_Var _ => #1
           | Core.Lit _ => #1
           | Core.App f a => exprSize f GHC.Num.+ exprSize a
           | Core.Lam b e => bndrSize b GHC.Num.+ exprSize e
           | Core.Let b e => bindSize b GHC.Num.+ exprSize e
           | Core.Case e b _ as_ =>
               ((exprSize e GHC.Num.+ bndrSize b) GHC.Num.+ #1) GHC.Num.+
               Data.Foldable.sum (GHC.Base.map altSize as_)
           | Core.Cast e _ => #1 GHC.Num.+ exprSize e
           | Core.Tick n e => tickSize n GHC.Num.+ exprSize e
           | Core.Type_ _ => #1
           | Core.Coercion _ => #1
           end with bindSize (arg_0__ : Core.CoreBind) : nat
                      := let pairSize (arg_0__ : (Core.Var * Core.CoreExpr)%type) : nat :=
                           let 'pair b e := arg_0__ in
                           bndrSize b GHC.Num.+ exprSize e in
                         match arg_0__ with
                         | Core.NonRec b e => bndrSize b GHC.Num.+ exprSize e
                         | Core.Rec prs => Data.Foldable.sum (GHC.Base.map pairSize prs)
                         end for bindSize.

Definition coreBindsSize : list Core.CoreBind -> nat :=
  fun bs => Data.Foldable.sum (GHC.Base.map bindSize bs).

Definition altSize : Core.CoreAlt -> nat :=
  fun '(pair (pair _ bs) e) => bndrsSize bs GHC.Num.+ exprSize e.

Definition altBndrStats : list Core.Var -> CoreStats :=
  fun vs => plusCS oneTM (sumCS (tyStats GHC.Base.∘ Core.varType) vs).

Definition bindStats : BasicTypes.TopLevelFlag -> Core.CoreBind -> CoreStats :=
  fix exprStats (arg_0__ : Core.CoreExpr) : CoreStats
        := let altStats (arg_0__ : Core.CoreAlt) : CoreStats :=
             let 'pair (pair _ bs) r := arg_0__ in
             plusCS (altBndrStats bs) (exprStats r) in
           match arg_0__ with
           | Core.Mk_Var _ => oneTM
           | Core.Lit _ => oneTM
           | Core.Type_ t => tyStats t
           | Core.Coercion c => coStats c
           | Core.App f a => plusCS (exprStats f) (exprStats a)
           | Core.Lam b e => plusCS (bndrStats b) (exprStats e)
           | Core.Let b e => plusCS (bindStats BasicTypes.NotTopLevel b) (exprStats e)
           | Core.Case e b _ as_ =>
               plusCS (plusCS (exprStats e) (bndrStats b)) (sumCS altStats as_)
           | Core.Cast e co => plusCS (coStats co) (exprStats e)
           | Core.Tick _ e => exprStats e
           end with bindStats (arg_0__ : BasicTypes.TopLevelFlag) (arg_1__ : Core.CoreBind)
                      : CoreStats
                      := let bindingStats (top_lvl : BasicTypes.TopLevelFlag)
                         (v : Core.Var)
                         (r : Core.CoreExpr)
                          : CoreStats :=
                           plusCS (letBndrStats top_lvl v) (exprStats r) in
                         match arg_0__, arg_1__ with
                         | top_lvl, Core.NonRec v r => bindingStats top_lvl v r
                         | top_lvl, Core.Rec prs =>
                             sumCS (fun '(pair v r) => bindingStats top_lvl v r) prs
                         end for bindStats.

Definition coreBindsStats : list Core.CoreBind -> CoreStats :=
  sumCS (bindStats BasicTypes.TopLevel).

Definition exprStats : Core.CoreExpr -> CoreStats :=
  fix exprStats (arg_0__ : Core.CoreExpr) : CoreStats
        := let altStats (arg_0__ : Core.CoreAlt) : CoreStats :=
             let 'pair (pair _ bs) r := arg_0__ in
             plusCS (altBndrStats bs) (exprStats r) in
           match arg_0__ with
           | Core.Mk_Var _ => oneTM
           | Core.Lit _ => oneTM
           | Core.Type_ t => tyStats t
           | Core.Coercion c => coStats c
           | Core.App f a => plusCS (exprStats f) (exprStats a)
           | Core.Lam b e => plusCS (bndrStats b) (exprStats e)
           | Core.Let b e => plusCS (bindStats BasicTypes.NotTopLevel b) (exprStats e)
           | Core.Case e b _ as_ =>
               plusCS (plusCS (exprStats e) (bndrStats b)) (sumCS altStats as_)
           | Core.Cast e co => plusCS (coStats co) (exprStats e)
           | Core.Tick _ e => exprStats e
           end with bindStats (arg_0__ : BasicTypes.TopLevelFlag) (arg_1__ : Core.CoreBind)
                      : CoreStats
                      := let bindingStats (top_lvl : BasicTypes.TopLevelFlag)
                         (v : Core.Var)
                         (r : Core.CoreExpr)
                          : CoreStats :=
                           plusCS (letBndrStats top_lvl v) (exprStats r) in
                         match arg_0__, arg_1__ with
                         | top_lvl, Core.NonRec v r => bindingStats top_lvl v r
                         | top_lvl, Core.Rec prs =>
                             sumCS (fun '(pair v r) => bindingStats top_lvl v r) prs
                         end for exprStats.

Definition altStats : Core.CoreAlt -> CoreStats :=
  fun '(pair (pair _ bs) r) => plusCS (altBndrStats bs) (exprStats r).

Definition bindingStats
   : BasicTypes.TopLevelFlag -> Core.Var -> Core.CoreExpr -> CoreStats :=
  fun top_lvl v r => plusCS (letBndrStats top_lvl v) (exprStats r).

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreStats.Outputable__CoreStats' *)

(* External variables:
     bool list nat op_zt__ orb pair unit BasicTypes.NotTopLevel BasicTypes.TopLevel
     BasicTypes.TopLevelFlag BasicTypes.isTopLevel Core.App Core.Case Core.Cast
     Core.Coercion Core.CoreAlt Core.CoreBind Core.CoreExpr Core.Id Core.Lam Core.Let
     Core.Lit Core.Mk_Var Core.NonRec Core.ProfNote Core.Rec Core.Tick Core.Tickish
     Core.Type_ Core.Var Core.isTyVar Core.varType Data.Foldable.foldl'
     Data.Foldable.sum GHC.Base.map GHC.Base.op_z2218U__ GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.default GHC.Num.fromInteger GHC.Num.op_zp__ Id.isJoinId
*)
