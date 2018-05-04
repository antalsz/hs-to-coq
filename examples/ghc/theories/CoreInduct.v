Require Import Core.
Require Import Coq.Lists.List.
Import ListNotations.

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

Require Import Coq.NArith.BinNat.

Local Open Scope N_scope.

Fixpoint core_size (e : CoreExpr) : N :=
  match e with
  | Mk_Var v => 0
  | Lit l => 0
  | App e1 e2 => core_size e1 + core_size e2 + 1
  | Lam v e => core_size e + 1
  | Let (NonRec v rhs) body => 
      core_size rhs + core_size body + 1
  | Let (Rec pairs) body => 
      fold_right N.add 0 (map (fun p => core_size (snd p)) pairs) +
      core_size body + 1
  | Case scrut bndr ty alts  => 
      fold_right N.add 0 (map (fun p => core_size (snd p)) alts) +
      core_size scrut + 1
  | Cast e _ =>   core_size e + 1
  | Tick _ e =>   core_size e + 1
  | Type_ _  =>   0
  | Coercion _ => 0
  end.  

(* For less obligations from [Program Fixpoint]: *)

Hint Resolve N.lt_wf_0 : arith.
