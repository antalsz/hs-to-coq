Require Import Core.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Psatz.

Require Import Omega.

Require Import Proofs.GHC.List.

Require Import Proofs.GhcTactics.
Require Import Proofs.Base.
Require Import Proofs.Core.


Set Bullet Behavior "Strict Subproofs".


Lemma core_induct' {b} :
  forall (e : Expr b)
  (P : Expr b -> Prop)
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
    - destruct b0 as [v rhs|pairs]; simpl.
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
Proof. exact core_induct'. Qed.

Section CoreLT.
  Context {v : Type}.
  
  (*

  Fixpoint core_size (e : Expr v) : nat :=
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
    *)
  
  (* We use the size only for comparisons. So lets
     make a definition here that we never unfold otherwise,
     and isntead create a tactic that handles all cases.
  *)
  Definition CoreLT := fun (x:Expr v) (y:Expr v) => core_size x < core_size y.

  Lemma CoreLT_wf : well_founded CoreLT.
  Proof.
    apply Wf_nat.well_founded_ltof. 
  Qed.

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


  Lemma core_size_mkLams_le:
    forall vs (rhs : Expr v),
    core_size rhs <= core_size (mkLams vs rhs).
  Proof.
    intros.
    induction vs.
    (* mkLams does not simplify automatically. *)
    * change (core_size rhs <= core_size rhs).
      lia.
    * change (core_size rhs <= S (core_size (mkLams vs rhs))).
      lia.
  Qed.

  Lemma CoreLT_let_rhs_mkLams:
    forall v vs rhs e,
    CoreLT rhs (Let (NonRec v (mkLams vs rhs)) e).
  Proof.
    intros.
    unfold CoreLT. simpl.
    apply Lt.le_lt_n_Sm.
    etransitivity; only 2: apply Plus.le_plus_l.
    apply core_size_mkLams_le.
  Qed.

  Lemma CoreLT_let_pairs_mkLam:
    forall v rhs vs pairs e,
    In (v, mkLams vs rhs) pairs ->
    CoreLT rhs (Let (Rec pairs) e).
  Proof.
    intros.
    unfold CoreLT. simpl.
    apply Lt.le_lt_n_Sm.
    etransitivity; only 2: apply Plus.le_plus_l.
    induction pairs; inversion H.
    * subst. simpl.
      pose proof (core_size_mkLams_le vs rhs).
      lia.
    * intuition. simpl. lia.
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
    HasNLams n e ->
    CoreLT e e' ->
    CoreLT (snd (collectNBinders n e)) e'.
  Proof.
    intros.
    cbv beta delta[collectNBinders].
    float_let.
    generalize (@nil v); intro args.
    revert args e H H0.
    generalize n; intro n'.
    induction n'; intros args e HLams Hlt.
    * destruct e; simpl; try apply Hlt.
    * destruct e; simpl; simpl in HLams; try contradiction.
      solve_error_sub.
      simpl. replace (n' - 0) with n'; try omega.
      apply IHn'; clear IHn'; cleardefs.
      auto.
      unfold CoreLT in *. simpl in *. lia.
  Qed.
End CoreLT.

(* For fewer obligations from [Program Fixpoint]: *)
Hint Resolve CoreLT_wf : arith.

(* This is a bit plump yet *)
Ltac Core_termination :=
  try solve [unfold CoreLT; simpl; lia]; 
  try (apply CoreLT_collectNBinders; only 1: assumption);
  first 
    [ apply CoreLT_let_rhs
    | apply CoreLT_let_rhs_mkLams
    | apply CoreLT_let_body
    | eapply CoreLT_let_pairs; eassumption
    | eapply CoreLT_let_pairs_mkLam; eassumption
    | eapply CoreLT_case_alts; eassumption
    ].

Opaque CoreLT.


(** And now the same for annotated core expressions *)
Section AnnCoreLT.
  Context {a v : Type}.
  Definition AnnCoreLT := fun (x y : AnnExpr a v) =>
     CoreLT (deAnnotate x) (deAnnotate y).

  Lemma AnnCoreLT_wf : well_founded AnnCoreLT.
  Proof.
    unfold AnnCoreLT.
    apply Inverse_Image.wf_inverse_image.
    apply CoreLT_wf.
  Qed.

  Lemma AnnCoreLT_case_alts:
    forall scrut b t alts dc pats rhs ann,
    In (dc, pats, rhs) alts ->
    AnnCoreLT rhs (ann, AnnCase scrut b t alts).
  Proof.
    intros.
    unfold AnnCoreLT.
    simpl.
    eapply CoreLT_case_alts.
    rewrite in_map_iff.
    exists (dc, pats, rhs).
    split; [reflexivity|assumption].
  Qed.

  Lemma AnnCoreLT_let_rhs:
    forall v rhs e fvs,
    AnnCoreLT rhs (fvs, AnnLet (AnnNonRec v rhs) e).
  Proof.
    intros.
    unfold AnnCoreLT. simpl.
    apply CoreLT_let_rhs.
  Qed.

  Lemma AnnCoreLT_let_pairs:
    forall v rhs pairs e fvs,
    In (v, rhs) pairs ->
    AnnCoreLT rhs (fvs, AnnLet (AnnRec pairs) e).
  Proof.
    intros.
    unfold AnnCoreLT. simpl.
    eapply CoreLT_let_pairs.
    rewrite flat_map_unpack_cons_f.
    rewrite in_map_iff.
    exists (v0, rhs).
    split; [reflexivity|assumption].
  Qed.


  Lemma AnnCoreLT_let_body:
    forall binds e fvs,
    AnnCoreLT e (fvs, AnnLet binds e).
  Proof. intros. unfold AnnCoreLT. simpl. destruct binds; apply CoreLT_let_body. Qed.

  (* Needs a precondition that there are enough lambdas *)
  Lemma AnnCoreLT_collectNAnnBndrs:
    forall n e e' `{GHC.Err.Default v},
    AnnHasNLams n e ->
    AnnCoreLT e e' ->
    AnnCoreLT (snd (collectNAnnBndrs n e)) e'.
  Proof.
    intros.
    unfold AnnCoreLT.
    rewrite deAnnotate_snd_collectNAnnBndrs by assumption.
    apply CoreLT_collectNBinders.
    + apply HasNLams_deAnnotate; assumption.
    + apply H1.
  Qed.

End AnnCoreLT.

(* For less obligations from [Program Fixpoint]: *)
Hint Resolve AnnCoreLT_wf : arith.

(* This is a bit plump yet *)
Ltac AnnCore_termination :=
  try (apply AnnCoreLT_collectNAnnBndrs; only 1: assumption);
  first 
    [ apply AnnCoreLT_let_rhs
    | apply AnnCoreLT_let_body
    | eapply AnnCoreLT_let_pairs; eassumption
    | eapply AnnCoreLT_case_alts; eassumption
    ].

