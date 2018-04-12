Require Import CoreSyn.
Require Import Id.
Require Import IdInfo.
Require Import VarSet.
Require Import BasicTypes.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Psatz.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

Require Import JoinPointInvariants.

(* This lemma exists, but is Opaque. No good for us. *)
Lemma  forallb_forall
     : forall (A : Type) (f : A -> bool) (l : list A),
       forallb f l = true <-> (forall x : A, In x l -> f x = true).
Proof.
  intros.
  induction l.
  * split; intro.
    - intros. inversion H0.
    - reflexivity.
  * split; intro.
    - simpl in H. rewrite andb_true_iff in H. destruct H.
      rewrite IHl in H0.
      intros. destruct H1.
      + subst. assumption.
      + intuition.
    - simpl. rewrite andb_true_iff. split.
      + apply H. left. reflexivity.
      + intuition.
Defined.


(* Attempt one: An inductive predicate *)
Inductive JoinPointsValid : CoreExpr -> Z -> VarSet -> Prop :=
  | JPV_Var     : forall v n jps,
    isJoinId v = false ->
    JoinPointsValid (Var v) n jps
  | JPV_JoinVar : forall v a n jps,
    isJoinId_maybe v = Some a ->
    a <= n ->
    elemVarSet v jps = true ->
    JoinPointsValid (Var v) n jps
  | JPV_List    : forall l n jps, JoinPointsValid (Lit l) n jps
  | JPV_App     : forall e1 e2 n jps,
    JoinPointsValid e1 (n+1) jps ->     (* Tail-call-position *)
    JoinPointsValid e2 0 emptyVarSet -> (* Non-tail-call position *)
    JoinPointsValid (App e1 e2) n jps
  | JPV_Lam     : forall v e n jps,
    JoinPointsValid e 0 emptyVarSet -> (* Non-tail-call position *)
    JoinPointsValid (Lam v e) n jps
  | JPV_LetNonRec  : forall v rhs body n jps, 
    isJoinId v = false ->
    JoinPointsValid rhs 0 emptyVarSet ->            (* Non-tail-call position *)
    JoinPointsValid body 0 (delVarSet jps v) ->     (* Tail-call-position *)
    JoinPointsValid (Let (NonRec v rhs) body) n jps
  | JPV_LetNonRecJP  : forall v a rhs body n jps, (* Shadowing *)
    isJoinId_maybe v = Some a ->
    GoodJoinRHS a rhs jps ->
    JoinPointsValid body 0 (extendVarSet jps v) ->     (* Tail-call-position *)
    JoinPointsValid (Let (NonRec v rhs) body) n jps
  | JPV_LetRec  : forall pairs body n jps,
    List.null pairs = false -> (* Not join-point-specific, could be its own invariant *)
    (forall v rhs, In (v,rhs) pairs -> isJoinId v = false) ->
    (forall v rhs, In (v,rhs) pairs -> JoinPointsValid rhs 0 emptyVarSet)  -> (* Non-tail-call position *)
    let jps' := delVarSetList jps (map fst pairs) in
    JoinPointsValid body 0 jps' ->     (* Tail-call-position *)
    JoinPointsValid (Let (Rec pairs) body) n jps
  | JPV_LetRecJP  : forall pairs body n jps, 
    List.null pairs = false -> (* Not join-point-specific, could be its own invariant *)
    (forall v rhs, In (v,rhs) pairs -> isJoinId v = true) ->
    let jps' := extendVarSetList jps (map fst pairs) in
    (forall v rhs a, In (v,rhs) pairs ->
                     isJoinId_maybe v = Some a ->
                     GoodJoinRHS a rhs jps')  -> (* Non-tail-call position *)
    JoinPointsValid body 0 jps' ->     (* Tail-call-position *)
    JoinPointsValid (Let (Rec pairs) body) n jps
  | JPV_Case  : forall scrut bndr ty alts n jps, 
    JoinPointsValid scrut 0 emptyVarSet -> (* Non-tail-call position *)
    let jps' := delVarSet jps bndr in
    (forall dc pats rhs, In (dc,pats,rhs) alts ->
                         let jps' := delVarSetList jps pats in
                         JoinPointsValid rhs 0 jps')  -> (* Tail-call position *)
    JoinPointsValid (Case scrut bndr ty alts) n jps
  | JPV_Cast  : forall e co n jps, 
    JoinPointsValid e 0 jps ->
    JoinPointsValid (Cast e co) n jps
  | JPV_Tick  : forall tickish e n jps, 
    JoinPointsValid e 0 jps ->
    JoinPointsValid (Tick tickish e) n jps
  | JPV_Type  : forall ty n jps, 
    JoinPointsValid (Type_ ty) n jps
  | JPV_Coercion  : forall co n jps, 
    JoinPointsValid (Coercion co) n jps
 with
  GoodJoinRHS : Z -> CoreExpr -> VarSet -> Prop :=
  | GJR_Lam : forall a v e jps,
    0 < a ->
    GoodJoinRHS (a - 1) e (delVarSet jps v) ->
    GoodJoinRHS a (Lam v e) jps
  | GJR_RHS: forall a e jps,
    a = 0 ->
    JoinPointsValid e 0 jps->     (* Tail-call-position *)
    GoodJoinRHS a e jps
  .

(* Attempt two: An executable checker *)


(* Relating the two definitions (may not be needed or useful) *)

Scheme JPV_mut := Induction for JoinPointsValid Sort Prop
with GJR_mut := Induction for GoodJoinRHS Sort Prop.

Axiom isJoinId_eq : forall v,
  isJoinId v = match isJoinId_maybe v with | None => false |Some _ => true end.

Axiom delVarList_singleton: forall jps v,
  delVarSetList jps (v :: nil) = delVarSet jps v.

Axiom extendVarList_singleton: forall jps v,
  extendVarSetList jps (v :: nil) = extendVarSet jps v.

Lemma bindersOf_cleanup:
  forall {a b} (pairs : list (a * b)),
  flat_map (fun '(binder, _) => binder :: nil) pairs = map fst pairs.
Proof. intros.  induction pairs. reflexivity. destruct a0. simpl. rewrite IHpairs. reflexivity. Qed.

Lemma JoinPointsValid_isJoinPointsValid:
  forall e n jps,
  JoinPointsValid e n jps -> isJoinPointsValid e n jps = true.
Proof.
  eapply JPV_mut with
    (P0 := fun a rhs jps _ => 
      (if a =? 0
        then isJoinPointsValid rhs 0 jps 
        else isJoinRHS a rhs jps) = true);
  intros; simpl;
  rewrite ?isJoinId_eq in *;
  rewrite ?orb_true_iff, ?andb_true_iff in *;
  rewrite ?bindersOf_cleanup.
  * destruct (isJoinId_maybe v); congruence.
  * rewrite e, andb_true_iff, Z.leb_le. split; assumption.
  * reflexivity.
  * split; assumption.
  * assumption.
  * destruct (isJoinId_maybe v); inversion_clear e.
    split; assumption.
  * rewrite e in *; clear e.
    split; assumption.
  * split; split.
    - rewrite negb_true_iff.
      assumption.
    - rewrite orb_true_iff. left.
      rewrite forallb_forall.
      intros [v rhs] HIn.
      erewrite e0 by eassumption.
      reflexivity.
    - rewrite forallb_forall.
      intros [v rhs] HIn.
      specialize (e0 _ _ HIn).
      rewrite isJoinId_eq in e0.
      destruct (isJoinId_maybe v); inversion_clear e0.
      specialize (H _ _ HIn).
      assumption.
    - enough (Htmp : (forallb (fun p : Var.Var * Expr CoreBndr => isJoinId (fst p)) pairs) = false)
         by (rewrite Htmp; assumption).
      apply not_true_is_false. intro Hforallb.
      rewrite forallb_forall in Hforallb.
      destruct pairs; only 1: inversion e.
      destruct p as [v rhs].
      specialize (e0 v rhs (or_introl eq_refl)).
      specialize (Hforallb (v, rhs) (or_introl eq_refl)).
      simpl in Hforallb.
      congruence.
  * assert (Hforallb: forallb (fun p : Var.Var * Expr CoreBndr => isJoinId (fst p)) pairs = true).
    { rewrite forallb_forall.
      intros [v rhs] HIn.
      erewrite e0 by eassumption.
      reflexivity. }
    rewrite Hforallb. clear Hforallb.
    split; split.
    - rewrite negb_true_iff.
      assumption.
    - rewrite orb_true_iff. right.
      reflexivity.
    - rewrite forallb_forall.
      intros [v rhs] HIn.
      specialize (e0 _ _ HIn).
      rewrite isJoinId_eq in e0.
      destruct (isJoinId_maybe v) eqn:HiJI; inversion_clear e0.
      specialize (H _ _ _ HIn HiJI).
      assumption.
    - rewrite ?orb_true_iff, ?andb_true_iff in *.
      assumption.
  * split.
    - assumption.
    - rewrite forallb_forall.
      intros [[dc pats] rhs] HIn.
      eapply H0; eassumption.
  * assumption.
  * assumption.
  * reflexivity.
  * reflexivity.
  * destruct (Z.eqb_spec a 0); try lia.
    destruct (Z.ltb_spec a 1); try lia. 
    destruct (Z.eqb_spec a 1).
    - destruct (Z.eqb_spec (a-1) 0); try lia.
      assumption.
    - destruct (Z.eqb_spec (a-1) 0); try lia.
      assumption.
  * destruct (Z.eqb_spec a 0); try lia.
    assumption.
Qed.

Lemma isJoinRHS_a_nonneg:
  forall a rhs jps, isJoinRHS a rhs jps = true -> 0 <= a.
Proof.
  intros.
  induction rhs; simpl in H; destruct (Z.ltb_spec a 1); try congruence.
  lia.
Qed.

Lemma isJoinPointsValid_JoinPointsValid:
  forall e n jps,
  isJoinPointsValid e n jps = true -> JoinPointsValid e n jps.
Proof.
  refine (fix IH e n jps (H : isJoinPointsValid e n jps = true)  {struct e} : JoinPointsValid e n jps := _
           with IHrhs a rhs jps (Hnn : a <> 0) (H : isJoinRHS a rhs jps = true) {struct rhs} : GoodJoinRHS a rhs jps := _
           for IH).
  * intros. destruct e; simpl in H; rewrite ?andb_true_iff in *.
    - destruct (isJoinId_maybe i) eqn:?.
      + rewrite ?andb_true_iff in *. destruct H.
        rewrite Z.leb_le in *.
        eapply JPV_JoinVar; try eassumption.
      + assert (isJoinId i = false) by (rewrite isJoinId_eq; rewrite Heqo; reflexivity).
        eapply JPV_Var; try eassumption.
   - constructor.
   - constructor; intuition.
   - constructor; intuition.
   - destruct b as [v rhs | pairs].
     + rewrite isJoinId_eq in H.
       destruct (isJoinId_maybe v) eqn:HJI; rewrite ?andb_true_iff in *.
       ** eapply JPV_LetNonRecJP.
          -- eassumption.
          -- destruct (Z.eqb_spec j 0).
             ++ eapply GJR_RHS; intuition.
             ++ apply IHrhs; intuition.
          -- apply IH; intuition.
       ** eapply JPV_LetNonRec.
          -- rewrite isJoinId_eq. rewrite HJI. reflexivity.
          -- intuition.
          -- intuition.
     + (* We must be careful to call IH and IHrhs only on arguments that
          are obviously elements of [pair], otherwise Coq will not accept
          this proof as structurally termination. *)
       assert (IH': forall v e n jps, In (v,e) pairs -> isJoinPointsValid e n jps = true -> JoinPointsValid e n jps).
       { clear -IH.
         intros. induction pairs; destruct H.
         - destruct a. specialize (IH e0 n jps). inversion H. subst; intuition.
         - intuition.
       }
       assert (IHrhs': forall v a rhs jps, In (v,rhs) pairs -> a <> 0 -> isJoinRHS a rhs jps = true -> GoodJoinRHS a rhs jps).
       { clear -IHrhs.
         intros. induction pairs; destruct H.
         - destruct a0. specialize (IHrhs a e jps). inversion H. subst; intuition.
         - intuition.
       }

      rewrite ?andb_true_iff in *.
       destruct H as [[??][??]].
       rewrite ?orb_true_iff in H0. destruct H0.
       ** rewrite negb_true_iff in H.
          rewrite forallb_forall in H0.
          rewrite forallb_forall in H1.

          assert (Hforallb : forallb (fun p : Var.Var * Expr CoreBndr => isJoinId (fst p)) pairs = false).
          {
             apply not_true_is_false. intro Hforallb.
             rewrite forallb_forall in Hforallb.
             destruct pairs; only 1: inversion H.
             destruct p as [v rhs].
             specialize (H0 (v, rhs) (or_introl eq_refl)).
             specialize (Hforallb (v, rhs) (or_introl eq_refl)).
             simpl in H0, Hforallb.
             rewrite negb_true_iff in H0.
             congruence.
          }

          eapply JPV_LetRec.
          -- assumption.
          -- intros v rhs HIn.
             specialize (H0 (v,rhs) HIn).
             rewrite negb_true_iff in H0.
             apply H0.
          -- intros v rhs HIn.
             specialize (H0 (v,rhs) HIn).
             rewrite negb_true_iff in H0. simpl in H0.
             rewrite isJoinId_eq in H0.
             specialize (H1 (v,rhs) HIn). simpl in H1.
             destruct (isJoinId_maybe v) eqn:HJI; inversion_clear H0.
             eapply IH'; eassumption.
          -- rewrite Hforallb in H2.
             eapply IH; eassumption.
       ** rewrite negb_true_iff in H.
          pose proof H0 as Hforallb. (* need this later *)
          rewrite forallb_forall in H0.
          rewrite forallb_forall in H1.

          eapply JPV_LetRecJP.
          -- assumption.
          -- intros v rhs HIn.
             specialize (H0 (v,rhs) HIn).
             apply H0.
          -- intros v rhs a HIn HJI.
             specialize (H0 (v,rhs) HIn).
             simpl in H0.
             rewrite isJoinId_eq in H0.
             specialize (H1 (v,rhs) HIn). simpl in H1.
             rewrite HJI in *.
             rewrite Hforallb in *.
             destruct (Z.eqb_spec a 0).
             ++ eapply GJR_RHS; try assumption.
                eapply IH'; eassumption.
             ++ eapply IHrhs'; eassumption.
          -- rewrite Hforallb in *.
             apply IH; assumption.
   - destruct H.
   
     (* We must be careful to call IH and IHrhs only on arguments that
        are obviously elements of [pair], otherwise Coq will not accept
        this proof as structurally termination. *)
     assert (IH': forall dc pats e n jps, In (dc,pats,e) l -> isJoinPointsValid e n jps = true -> JoinPointsValid e n jps).
     { clear -IH.
       intros. induction l; destruct H.
       - destruct a as [[dc' pats'] e']. specialize (IH e' n jps). inversion H. subst; intuition.
       - intuition.
     }   
   
     constructor.
     + apply IH; assumption.
     + intros dc pats rhs Hin.
       rewrite forallb_forall in H0.
       specialize (H0 (dc, pats, rhs) Hin). simpl in H0.
                Guarded.
       eapply IH'; eassumption.
   - constructor; intuition.
   - constructor; intuition.
   - constructor; intuition.
   - constructor; intuition.
 * destruct rhs; simpl in H; destruct (Z.ltb_spec a 1); try congruence.
   eapply GJR_Lam. lia.
   destruct (Z.eqb_spec a 1).
   + apply GJR_RHS. lia. apply IH. assumption.
   + apply IHrhs. lia. assumption. 
Qed.