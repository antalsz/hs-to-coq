Require Import Prelude.
Require Import Lambda.

Definition isVal (e : Expr) : Prop :=
  match e with
    | Mk_Var _ => True
    | Mk_Lam _ _ => True
    | _ => False
  end.


Fixpoint rename v w body := match body with
  | Mk_Var v' => Mk_Var (if v == v' then w else v')
  | Mk_Lam v' e => Mk_Lam v' (if v == v' then e else rename v w e)
  | Mk_App e1 e2 => Mk_App (rename v w e1)  (rename v w e2)
  | Mk_Let v' rhs body => Mk_Let v' (rename v w rhs) (if v == v' then body else rename v w body)
end.

Fixpoint depth e := match e with 
  | Mk_Var v' => 0
  | Mk_Lam v' e => S (depth e)
  | Mk_App e1 e2 => PeanoNat.Nat.max (S (depth e1)) (S (depth e2))
  | Mk_Let v' rhs body =>  PeanoNat.Nat.max (S (depth rhs)) (S (depth body))
end.

Lemma depth_rename : forall v w e, depth (rename v w e) = depth e.
Proof.
  intros.
  induction e.
  * auto.
  * simpl.
    destruct (negb (v =? n)%Z).
    + rewrite IHe1. auto.
    + rewrite IHe1. rewrite IHe2. auto.
  * simpl.
    destruct (negb (v =? n)%Z).
    + auto.
    + rewrite IHe. auto.
  * simpl.
    rewrite IHe1. rewrite IHe2.
    auto.
Qed.

Require Import Recdef.


Function subst v arg body {measure depth body} := match body with
  | Mk_Var v' => if v == v' then arg else Mk_Var v'
  | Mk_Lam v' e => if v == v' then Mk_Lam v' e else
    let f := fresh e in
    Mk_Lam f (subst v arg (rename v' v e))
  | Mk_App e1 e2 => Mk_App (subst v arg e1)  (subst v arg e2)
  | Mk_Let v' rhs body =>
    let v'' := fresh body in
    let rhs' := subst v arg rhs in
    let body' := subst v arg (rename v' v'' body) in
    Mk_Let v' rhs' body'
end.
Proof.
 all: intros; simpl; repeat rewrite depth_rename; zify; omega.
Qed.

Inductive ss : Expr -> Expr -> Prop :=
  | ss_beta : forall v body arg, isVal arg -> ss (Mk_App (Mk_Lam v body) arg) (subst v arg body)
  | ss_let: forall v body rhs , isVal rhs -> ss (Mk_Let v rhs body) (subst v rhs body)
  | ss_let_search: forall v body rhs rhs', ss rhs rhs' -> ss (Mk_Let v rhs body) (Mk_Let v rhs' body)
  | ss_app_search : forall m m' n, ss m m' -> ss (Mk_App m n) (Mk_App m' n)
  | ss_app_val: forall m n n', isVal m -> ss n n' -> ss (Mk_App m n) (Mk_App m n')
.

