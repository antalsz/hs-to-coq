Require Import CoreSyn.
Require Import Coq.Lists.List.
Import ListNotations.

Set Bullet Behavior "Strict Subproofs".


Lemma core_induct :
  forall (e : CoreExpr)
  (P : CoreExpr -> Prop)
  (HVar  : forall v, P (Var v))
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
