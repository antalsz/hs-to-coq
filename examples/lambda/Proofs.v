Require Import Prelude.
Require Import Lambda.

Require Import Recdef.

Set Bullet Behavior "Strict Subproofs".

Definition isVal (e : Expr) : Prop :=
  match e with
    | Var _ => True
    | Lam _ _ => True
    | _ => False
  end.

Definition rename : Name -> Name -> Expr -> Expr :=
  fix rename v w body
        := match body with
             | Var v' => Var (if v == v' then w else v')
             | Lam v' e => Lam v' (if v == v' then e else rename v w e)
             | App e1 e2 => App (rename v w e1) (rename v w e2)
             | Let v' rhs body => Let v' (rename v w rhs) (if v == v'
                                                          then body
                                                          else rename v w body)
           end.



Fixpoint depth e : nat := match e with
  | Var v' => 0
  | Lam v' e => S (depth e)
  | App e1 e2 =>
    Nat.max (S (depth e1)) (S (depth e2))
  | Let v' rhs body =>
    Nat.max (S (depth rhs)) (S (depth body))
end.


Lemma depth_rename : forall v w e,
    depth (rename v w e) = depth e.
Proof.
  intros.
  induction e.
  * auto.
  * simpl.
    destruct (v == n).
    + rewrite IHe1. auto.
    + rewrite IHe1. rewrite IHe2. auto.
  * simpl.
    destruct (v == n).
    + auto.
    + rewrite IHe. auto.
  * simpl.
    rewrite IHe1. rewrite IHe2.
    auto.
Qed.




Function subst v arg body {measure depth body} :=
  match body with
  | Var v' => if v == v' then arg else Var v'
  | Lam v' e => if v == v' then Lam v' e else
                    let f := fresh e in
                    Lam f (subst v arg (rename v' v e))
  | App e1 e2 => App (subst v arg e1)  (subst v arg e2)
  | Let v' rhs body =>
    let v'' := fresh body in
    let rhs' := subst v arg rhs in
    let body' := subst v arg (rename v' v'' body) in
    Let v' rhs' body'
  end.
Proof.
  all: intros; simpl;
    repeat rewrite depth_rename; zify; omega.
Qed.

Inductive small_step : Expr -> Expr -> Prop :=
| ss_beta : forall v body arg,
    isVal arg ->
    small_step (App (Lam v body) arg) (subst v arg body)
| ss_let: forall v body rhs ,
    isVal rhs ->
    small_step (Let v rhs body) (subst v rhs body)
| ss_let_search: forall v body rhs rhs',
    small_step rhs rhs' ->
    small_step (Let v rhs body) (Let v rhs' body)
| ss_app_search : forall m m' n,
    small_step m m' ->
    small_step (App m n) (App m' n)
| ss_app_val: forall m n n',
    isVal m ->
    small_step n n' ->
    small_step (App m n) (App m n').


Fixpoint small_step_fun (t : Expr) : option Expr :=
  match t with
  | App t1 t2 => match t1 with
                | Lam v t3 =>
                  match small_step_fun t2 with
                  | Some t2' => Some (App t1 t2')
                  | _ => match t2 with
                        | App _ _ => None
                        | Let _ _ _ => None
                        | _ => Some (subst v t2 t3)
                        end
                  end
                | Var i =>
                  match small_step_fun t2 with
                    | Some t2' => Some (App t1 t2')
                    | _ => None
                    end
                | _ => match (small_step_fun t1) with
                      | Some t1' => Some (App t1' t2)
                      | _ => None
                      end
                   end
  | Let v t1 t2 =>
    match t1 with
      | Var _ => Some (subst v t1 t2)
      | Lam _ _ => Some (subst v t1 t2)
      | _ => match (small_step_fun t1) with
            | Some t1' => Some (Let v t1' t2)
            | _ => None
            end
    end
  | _ => None
  end.

Lemma isVal_not_step: forall n,
    isVal n -> small_step_fun n = None.
Proof.
  intros []; auto;
  intros H; inversion H.
Qed.

Lemma fun_step : forall  k m m', (k = depth m)%nat ->
  small_step_fun m = Some m' -> small_step m m'.
Proof.
  intro k.
  induction (lt_wf k) as [n _ IH].
  intros m m' Heq SS.
  destruct m; simpl in *; subst; try solve [inversion SS].
  - (* let *)
    destruct m1.
    + inversion SS.
      eapply ss_let; simpl; auto.
    + destruct (small_step_fun (Let n m1_1 m1_2)) eqn:J; inversion SS.
      eapply ss_let_search.
      eapply (IH (depth (Let n m1_1 m1_2))); auto.
      zify; omega.
    + inversion SS.
      eapply ss_let; simpl; auto.
    + destruct (small_step_fun (App m1_1 m1_2)) eqn:J; inversion SS.
      eapply ss_let_search.
      eapply (IH (depth (App m1_1 m1_2))); auto.
      zify; omega.
  -  (* app *)
    destruct m1.
    + destruct (small_step_fun m2) eqn:J; inversion SS.
      eapply ss_app_val.
      simpl; auto.
      eapply (IH (depth m2)); simpl; auto.
    + destruct (small_step_fun (Let n m1_1 m1_2)) eqn:J; inversion SS.
      eapply ss_app_search.
      eapply (IH (depth (Let n m1_1 m1_2))); auto.
      zify; omega.
    + destruct (small_step_fun m2) eqn:J; inversion SS.
      eapply ss_app_val.
      simpl; auto.
      eapply (IH (depth m2)); auto.
      zify; omega.
      destruct m2;
        try solve [inversion SS; eapply ss_beta; simpl; auto].
    + destruct (small_step_fun (App m1_1 m1_2)) eqn:J; inversion SS.
      eapply ss_app_search.
      eapply (IH (depth (App m1_1 m1_2))); auto.
      zify; omega.
Qed.

Lemma small_step_small_step_fun : forall m m',
  small_step m m' <-> small_step_fun m = Some m'.
Proof.
  split.
  - induction 1; simpl.
    + (* beta *) rewrite isVal_not_step; auto.
      destruct arg; auto; inversion H.
    + (* let *) destruct rhs; auto;
        inversion H; subst.
    + (* let search *) destruct rhs; auto; try solve [inversion H];
        rewrite IHsmall_step; auto.
    + (* app search *)
      destruct m; try solve [inversion IHsmall_step];
      rewrite IHsmall_step; auto.
    + (* app val *)
      destruct m; try solve [inversion H];
      rewrite IHsmall_step; auto.
  - eapply fun_step. eauto.
Qed.

(*
Inductive rtc {A} (R:A -> A -> Prop) : A -> A -> Prop :=
| rtc_refl : forall a, rtc R a a
| rtc_step : forall a b c, R a b -> rtc R b c -> rtc R a c.

Notation "R ^*" := (rtc R) (at level 1, format "R ^*").

Definition nf (x: Expr): Prop := ~ exists y, small_step x y.
*)

(*
Inductive beta_equiv : Expr -> Expr -> Prop :=
| be_refl: forall x, beta_equiv x y
| be_Step: forall v x y,
    beta_equiv (Let v x y) (App (Lam v y) x)

| be_Var : forall v, beta_equiv (Var v) (Var v)
| be_Let: forall v x1 x2 y1 y2,
    beta_equiv x1 x2 -> beta_equiv y1 y2 ->
    beta_equiv (Let v x1 y1) (Let v x2 y2)
| be_App: forall x1 x2 y1 y2,
    beta_equiv x1 x2 -> beta_equiv y1 y2 ->
    beta_equiv (App x1 y1) (App x2 y2)
| be_Lam: forall v x1 x2,
    beta_equiv x1 x2 ->
    beta_equiv (Lam v x1) (Lam v x2).

| ss_beta : forall v body arg,
    isVal arg ->
    small_step (App (Lam v body) arg) (subst v arg body)
| ss_let: forall v body rhs ,
    isVal rhs ->
    small_step (Let v rhs body) (subst v rhs body)
*)
(*
Let x y z ==  App (Lam x z)  y



    Lam x (App x (Lam y y)) is nf
anf (Lam x (App x (Lam y y))) =
     Lam x (Let z = (Lam y y) in x z)
*)
(*
Theorem anf_correct: forall x y,
    small_step^* x y -> nf y ->
    small_step^* (anf x) y' /\ R y y'.
Proof.
  intros x y Hs Hn.
*)