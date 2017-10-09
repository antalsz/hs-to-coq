(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted imports: *)

Require GHC.Num.

(* Converted declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom patternFailure : forall {a}, a.

Inductive Expr : Type := Mk_Val : GHC.Num.Int -> Expr
                      |  Mk_Add : Expr -> Expr -> Expr.

Definition eval : Expr -> GHC.Num.Int :=
  fix eval arg_10__
        := match arg_10__ with
             | (Mk_Val n) => n
             | (Mk_Add x y) => GHC.Num.op_zp__ (eval x) (eval y)
           end.

Inductive Op : Type := Mk_PUSH : GHC.Num.Int -> Op
                    |  Mk_ADD : Op.

Definition Code :=
  list Op%type.

Definition comp' : Expr -> Code -> Code :=
  fix comp' arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | (Mk_Val n) , c => cons (Mk_PUSH n) c
             | (Mk_Add x y) , c => comp' x (comp' y (cons Mk_ADD c))
           end.

Definition Stack :=
  list GHC.Num.Int%type.

Definition exec : Code -> Stack -> Stack :=
  fix exec arg_5__ arg_6__
        := match arg_5__ , arg_6__ with
             | nil , s => s
             | (cons (Mk_PUSH n) c) , s => exec c (cons n s)
             | (cons Mk_ADD c) , (cons m (cons n s)) => exec c (cons (GHC.Num.op_zp__ n m) s)
             | _ , _ => patternFailure
           end.

(* Unbound variables:
     GHC.Num.Int GHC.Num.op_zp__ cons list
*)
