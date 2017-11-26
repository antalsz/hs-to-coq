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
  | Mk_App e1 e2 =>
    PeanoNat.Nat.max (S (depth e1)) (S (depth e2))
  | Mk_Let v' rhs body =>
    PeanoNat.Nat.max (S (depth rhs)) (S (depth body))
end.

Lemma depth_rename : forall v w e,
    depth (rename v w e) = depth e.
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


Function subst v arg body {measure depth body} :=
  match body with
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
  all: intros; simpl;
    repeat rewrite depth_rename; zify; omega.
Qed.

Inductive small_step : Expr -> Expr -> Prop :=
| ss_beta : forall v body arg,
    isVal arg ->
    small_step (Mk_App (Mk_Lam v body) arg) (subst v arg body)
| ss_let: forall v body rhs ,
    isVal rhs ->
    small_step (Mk_Let v rhs body) (subst v rhs body)
| ss_let_search: forall v body rhs rhs',
    small_step rhs rhs' ->
    small_step (Mk_Let v rhs body) (Mk_Let v rhs' body)
| ss_app_search : forall m m' n,
    small_step m m' ->
    small_step (Mk_App m n) (Mk_App m' n)
| ss_app_val: forall m n n',
    isVal m ->
    small_step n n' ->
    small_step (Mk_App m n) (Mk_App m n').


Fixpoint small_step_fun (t : Expr) : option Expr :=
  match t with
  | Mk_App t1 t2 => match t1 with
                | Mk_Lam v t3 =>
                  match small_step_fun t2 with
                  | Some t2' => Some (Mk_App t1 t2')
                  | _ => match t2 with
                        | Mk_App _ _ => None
                        | _ => Some (subst v t2 t3)
                        end
                  end
                | Mk_Var i =>
                  match small_step_fun t2 with
                    | Some t2' => Some (Mk_App t1 t2')
                    | _ => None
                    end
                | _ => match (small_step_fun t1) with
                      | Some t1' => Some (Mk_App t1' t2)
                      | _ => None
                      end
                   end
  | Mk_Let v t1 t2 =>
    match t1 with
      | Mk_Var _ => Some (subst v t1 t2)
      | Mk_Lam _ _ => Some (subst v t1 t2)
      | _ => match (small_step_fun t1) with
            | Some t1' => Some (Mk_Let v t1' t2)
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


Lemma small_step_small_step_fun : forall m m',
  small_step m m' <-> small_step_fun m = Some m'.
Proof.
  split.
  - induction 1.
    + simpl. rewrite isVal_not_step; auto.
      destruct arg; auto. inversion H.
    + simpl.
      destruct rhs; auto;
        inversion H; subst.
    + inversion H; subst.
      * simpl in IHsmall_step.
        simpl.
        destruct (small_step_fun arg).
        -- inversion IHsmall_step; auto.
        -- destruct arg; auto. inversion IHsmall_step.
      * simpl in IHsmall_step.
        simpl.
        destruct rhs0; auto.
        -- destruct (small_step_fun (Mk_Let n rhs0_1 rhs0_2)).
           inversion IHsmall_step. auto.
        -- inversion IHsmall_step.
      * destruct (small_step_fun (Mk_App rhs0_1 rhs0_2));
          inversion IHsmall_step; auto.
      * simpl in IHsmall_step.
        simpl.        
        destruct rhs0.
        -- inversion IHsmall_step. auto.
        -- destruct (small_step_fun (Mk_Let n rhs0_1 rhs0_2)).
           inversion IHsmall_step. auto.
        -- inversion IHsmall_step.
        -- inversion IHsmall_step. auto.
        -- destruct (small_step_fun (Mk_App rhs0_1 rhs0_2));
             inversion IHsmall_step; auto.
        - simpl in IHsmall_step.
           simpl.
           destruct m; try solve [inversion H0].
           ++ destruct (small_step_fun (Mk_Let n0 m1 m2));
                inversion IHsmall_step; subst; auto.
           ++ destruct (small_step_fun (Mk_App m1 m2));
                inversion IHsmall_step; auto.
        -- simpl in IHsmall_step.
           simpl.
           destruct m; try solve [inversion H0].
           ++ destruct (small_step_fun n);
                inversion IHsmall_step; subst; auto.
           ++ destruct (small_step_fun n);
                inversion IHsmall_step; subst; auto.
              destruct n;
                try solve [inversion H1| inversion H3].
              inversion H3. auto.
        -- destruct m;
             try solve [inversion IHsmall_step];
                 simpl in IHsmall_step;
                 simpl.
           ++ destruct m1; inversion IHsmall_step; auto.
              ** destruct (small_step_fun
                             (Mk_Let n1 m1_1 m1_2));
                   inversion IHsmall_step; auto.
              ** destruct (small_step_fun
                             (Mk_App m1_1 m1_2));
                   inversion IHsmall_step; auto.
        + simpl. simpl in IHsmall_step.
              intuition.
              ** inversion IHsmall_step. subst. auto.
              **  admit.
                  admit.
                  admit.
Admitted.


Inductive rtc {A} (R:A -> A -> Prop) : A -> A -> Prop :=
| rtc_refl : forall a, rtc R a a
| rtc_step : forall a b c, R a b -> rtc R b c -> rtc R a c.

Notation "R ^*" := (rtc R) (at level 1, format "R ^*").

Definition nf (x: Expr): Prop := ~ exists y, small_step x y.

Inductive beta_equiv : Expr -> Expr -> Prop :=
| be_refl: forall x, beta_equiv x y
| be_
| be_Step: forall v x y,
    beta_equiv (Mk_Let v x y) (Mk_App (Mk_Lam v y) x)
               
| be_Var : forall v, beta_equiv (Mk_Var v) (Mk_Var v)
| be_Let: forall v x1 x2 y1 y2,
    beta_equiv x1 x2 -> beta_equiv y1 y2 ->
    beta_equiv (Mk_Let v x1 y1) (Mk_Let v x2 y2)
| be_App: forall x1 x2 y1 y2,
    beta_equiv x1 x2 -> beta_equiv y1 y2 ->
    beta_equiv (Mk_App x1 y1) (Mk_App x2 y2)
| be_Lam: forall v x1 x2,
    beta_equiv x1 x2 ->
    beta_equiv (Mk_Lam v x1) (Mk_Lam v x2).
                           
| ss_beta : forall v body arg,
    isVal arg ->
    small_step (Mk_App (Mk_Lam v body) arg) (subst v arg body)
| ss_let: forall v body rhs ,
    isVal rhs ->
    small_step (Mk_Let v rhs body) (subst v rhs body)

(* 
Let x y z ==  App (Lam x z)  y



    Lam x (App x (Lam y y)) is nf
anf (Lam x (App x (Lam y y))) = 
     Lam x (Let z = (Lam y y) in x z)
*)
Theorem anf_correct: forall x y,
    small_step^* x y -> nf y ->
    small_step^* (anf x) y' /\ R y y'.
Proof.
  intros x y Hs Hn.
  
  