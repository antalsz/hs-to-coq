Require Import Core.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Tactics.

Set Bullet Behavior "Strict Subproofs".


Lemma core_induct :
  forall (e : CoreExpr)
  (P : CoreExpr -> Prop)
  (HVar  : forall v, P (Mk_Var v))
  (HLit  : forall l, P (Lit l))
  (HApp  : forall e1 e2, P e1 -> P e2 -> P (App e1 e2))
  (HLam  : forall v e, P e -> P (Lam v e))
  (HLet  : forall binds body,
      (match binds with
       | NonRec v rhs => P rhs
       | Rec pairs    => (forall v rhs, In (v, rhs) pairs -> P rhs)
       end) ->
      P body ->
      P (Let binds body))
  (HCase : forall scrut bndr ty alts, P scrut -> (forall dc pats rhs, In (dc, pats ,rhs) alts -> P rhs) -> P (Case scrut bndr ty alts))
  (HCast : forall e co, P e -> P (Cast e co))
  (HTick : forall tickish e, P e -> P (Tick tickish e))
  (HType : forall ty, P (Type_ ty))
  (HCoercion : forall co, P (Coercion co)),
  P e.
Proof.
  intros.
  revert e.
  fix IH 1.
  intro e.
  destruct e.
  * apply HVar.
  * apply HLit.
  * apply HApp; apply IH.
  * apply HLam; apply IH.
  * apply HLet.
    - destruct b as [v rhs|pairs]; simpl.
      + simpl.
        apply IH.
      + induction pairs as [|[v rhs] pairs']; simpl.
        ** intros ?? [].
        ** intros v' rhs' [Heq|HIn].
           ++ inversion Heq.
              rewrite <- H1.
              apply IH.
           ++ eapply IHpairs'. eassumption.
    - apply IH.
  * apply HCase.
    - apply IH.
    - induction l as [| [[dc pats] rhs] alts'].
      ** intros ??? [].
      ** intros ??? [Heq|HIn].
         ++ inversion Heq.
            rewrite <- H2.
            apply IH.
         ++ eapply IHalts'. eassumption.
  * apply HCast; apply IH.
  * apply HTick; apply IH.
  * apply HType.
  * apply HCoercion.
Qed.

Fixpoint core_size (e : CoreExpr) : nat :=
  match e with
  | Mk_Var v => 0
  | Lit l => 0
  | App e1 e2 => S (core_size e1 + core_size e2)
  | Lam v e => S (core_size e)
  | Let (NonRec v rhs) body => 
      S (core_size rhs + core_size body)
  | Let (Rec pairs) body => 
      S (fold_right plus 0 (map (fun p => core_size (snd p)) pairs) +
         core_size body)
  | Case scrut bndr ty alts  => 
      S (core_size scrut +
         fold_right plus 0 (map (fun p => core_size (snd p)) alts))
  | Cast e _ =>   S (core_size e)
  | Tick _ e =>   S (core_size e)
  | Type_ _  =>   0
  | Coercion _ => 0
  end.

(* We use the size only for comparisons. So lets
   make a definition here that we never unfold otherwise,
   and isntead create a tactic that handles all cases.
*)
Definition CoreLT := fun x y => core_size x < core_size y.

Lemma CoreLT_wf : well_founded CoreLT.
Proof.
  apply Wf_nat.well_founded_ltof. 
Qed.

(* For less obligations from [Program Fixpoint]: *)
Hint Resolve CoreLT_wf : arith.

Require Import Psatz.

Lemma CoreLT_case_alts:
  forall scrut b t alts dc pats rhs,
  In (dc, pats, rhs) alts ->
  CoreLT rhs (Case scrut b t alts).
Proof.
  intros.
  unfold CoreLT. simpl.
  apply Lt.le_lt_n_Sm.
  etransitivity; only 2: apply Plus.le_plus_r.
  induction alts; inversion H.
  * subst. simpl. lia.
  * intuition. simpl. lia.
Qed.


Lemma CoreLT_let_rhs:
  forall v rhs e,
  CoreLT rhs (Let (NonRec v rhs) e).
Proof.
  intros.
  unfold CoreLT. simpl.
  apply Lt.le_lt_n_Sm.
  etransitivity; only 2: apply Plus.le_plus_l.
  lia.
Qed.


Lemma CoreLT_let_pairs:
  forall v rhs pairs e,
  In (v, rhs) pairs ->
  CoreLT rhs (Let (Rec pairs) e).
Proof.
  intros.
  unfold CoreLT. simpl.
  apply Lt.le_lt_n_Sm.
  etransitivity; only 2: apply Plus.le_plus_l.
  induction pairs; inversion H.
  * subst. simpl. lia.
  * intuition. simpl. lia.
Qed.


Lemma CoreLT_let_body:
  forall binds e,
  CoreLT e (Let binds e).
Proof. intros. unfold CoreLT. simpl. destruct binds; lia. Qed.

(* Needs a precondition that there are enough lambdas *)
Lemma CoreLT_collectNBinders:
  forall n e e',
  CoreLT e e' ->
  CoreLT (snd (collectNBinders n e)) e'.
Proof.
  intros.
  cbv beta delta[collectNBinders].
  float_let.
  generalize (@nil CoreBndr); intro args.
  generalize n; intro n'.
  revert args e H.
  induction n'; intros.
  * destruct e; simpl; try apply H.
  * destruct e; simpl.
    Focus 4. apply IHn'. clear IHn'. cleardefs.
    unfold CoreLT in *. simpl in *. lia.
Admitted.

(* This is a bit plump yet *)
Ltac Core_termination :=
  try apply CoreLT_collectNBinders;
  first 
    [ apply CoreLT_let_rhs
    | apply CoreLT_let_body
    | eapply CoreLT_let_pairs; eassumption
    | eapply CoreLT_case_alts; eassumption
    ].

  