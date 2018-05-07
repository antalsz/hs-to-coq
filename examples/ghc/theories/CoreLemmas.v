Require Import Core.

Set Bullet Behavior "Strict Subproofs".

Open Scope nat_scope.
Fixpoint HasNLams {v : Type} (n : nat) (e : Expr v) : Prop :=
  match n, e with
  | 0, _ => True
  | S n, Lam _ e => HasNLams n e
  | _, _ => False
  end.
