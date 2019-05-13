(* NOTE THIS FILE IS NOT USED. Delete? *)

Require Import Id.
Require Import Core.
Require Import BasicTypes.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Psatz.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

Require Import JoinPointInvariants.
Require Import CoreInduct.

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
    JoinPointsValid (Mk_Var v) n jps
  | JPV_JoinVar : forall v a n jps,
    isJoinId_maybe v = Some a ->
    a <= n ->
    elemVarSet v jps = true ->
    JoinPointsValid (Mk_Var v) n jps
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

Axiom isJoinId_eq : forall v,  (* in unused code *)
  isJoinId v = match isJoinId_maybe v with | None => false |Some _ => true end.

Axiom delVarList_singleton: forall jps v, (* in unused code *)
  delVarSetList jps (v :: nil) = delVarSet jps v.

Axiom extendVarList_singleton: forall jps v, (* in unused code *)
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
  rewrite ?bindersOf_cleanup; fold isJoinPointsValidPair.
  * destruct (isJoinId_maybe v); congruence.
  * rewrite e, andb_true_iff, Z.leb_le. split; assumption.
  * reflexivity.
  * split; assumption.
  * assumption.
  * unfold isJoinPointsValidPair,  isJoinPointsValidPair_aux.
    destruct (isJoinId_maybe v); inversion_clear e.
    split; assumption.
  * unfold isJoinPointsValidPair,  isJoinPointsValidPair_aux.
    rewrite e in *; clear e.
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
      unfold isJoinPointsValidPair,  isJoinPointsValidPair_aux.
      specialize (e0 _ _ HIn).
      rewrite isJoinId_eq in e0.
      destruct (isJoinId_maybe v); inversion_clear e0.
      specialize (H _ _ HIn).
      assumption.
    - enough (Htmp : (forallb (fun p : Core.Var * Expr CoreBndr => isJoinId (fst p)) pairs) = false)
         by (rewrite Htmp; assumption).
      apply not_true_is_false. intro Hforallb.
      rewrite forallb_forall in Hforallb.
      destruct pairs; only 1: inversion e.
      destruct p as [v rhs].
      specialize (e0 v rhs (or_introl eq_refl)).
      specialize (Hforallb (v, rhs) (or_introl eq_refl)).
      simpl in Hforallb.
      congruence.
  * assert (Hforallb: forallb (fun p : Core.Var * Expr CoreBndr => isJoinId (fst p)) pairs = true).
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
      unfold isJoinPointsValidPair,  isJoinPointsValidPair_aux.
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
  intro e.
  enough ((forall n jps (HiJPV : isJoinPointsValid e n jps = true), JoinPointsValid e n jps)
      /\  (forall a jps (Hnn : a <> 0) (HiJR : isJoinRHS a e jps = true), GoodJoinRHS a e jps))
       by apply H.
  induction e using core_induct;
    (split; intros;
      [ simpl in HiJPV; rewrite ?andb_true_iff in *
      | simpl in HiJR; try solve [destruct (Z.ltb_spec a 1); inversion HiJR]]).
  * destruct (isJoinId_maybe v) eqn:?.
    + rewrite ?andb_true_iff in *. destruct HiJPV.
      rewrite Z.leb_le in *.
      eapply JPV_JoinVar; try eassumption.
    + assert (isJoinId v = false) by (rewrite isJoinId_eq; rewrite Heqo; reflexivity).
      eapply JPV_Var; try eassumption.
 * constructor.
 * constructor; intuition.
 * constructor; intuition.

 * simpl in HiJR; destruct (Z.ltb_spec a 1); try congruence.
   eapply GJR_Lam. lia.
   destruct (Z.eqb_spec a 1).
   + apply GJR_RHS. lia. apply IHe. assumption.
   + apply IHe. lia. assumption. 
 
 * destruct binds as [v rhs | pairs].
   + rewrite isJoinId_eq in HiJPV.
     unfold isJoinPointsValidPair,  isJoinPointsValidPair_aux in *.
     destruct (isJoinId_maybe v) eqn:HJI; rewrite ?andb_true_iff in *.
     ** eapply JPV_LetNonRecJP.
        -- eassumption.
        -- destruct (Z.eqb_spec j 0).
           ++ apply GJR_RHS. assumption. apply H. intuition.
           ++ apply H. assumption. intuition.
        -- apply IHe; intuition.
     ** eapply JPV_LetNonRec.
        -- rewrite isJoinId_eq. rewrite HJI. reflexivity.
        -- apply H. intuition.
        -- intuition.
   + rewrite ?andb_true_iff in *.
     destruct HiJPV as [[??][??]].
     rewrite ?orb_true_iff in H1. destruct H1.
     ** rewrite negb_true_iff in H0.
        rewrite forallb_forall in H1.
        rewrite forallb_forall in H2.

        assert (Hforallb : forallb (fun p : Core.Var * Expr CoreBndr => isJoinId (fst p)) pairs = false).
        {
           apply not_true_is_false. intro Hforallb.
           rewrite forallb_forall in Hforallb.
           destruct pairs; only 1: inversion H0.
           destruct p as [v rhs].
           specialize (H1 (v, rhs) (or_introl eq_refl)).
           specialize (Hforallb (v, rhs) (or_introl eq_refl)).
           simpl in H1, Hforallb.
           rewrite negb_true_iff in H1.
           congruence.
        }

        eapply JPV_LetRec.
        -- assumption.
        -- intros v rhs HIn.
           specialize (H1 (v,rhs) HIn).
           rewrite negb_true_iff in H1.
           apply H1.
        -- intros v rhs HIn.
           specialize (H1 (v,rhs) HIn).
           rewrite negb_true_iff in H1. simpl in H1.
           rewrite isJoinId_eq in H1.
           specialize (H2 (v,rhs) HIn). simpl in H2.
           unfold isJoinPointsValidPair,  isJoinPointsValidPair_aux in *.
           destruct (isJoinId_maybe v) eqn:HJI; inversion_clear H1.
           eapply H; eassumption.
        -- rewrite Hforallb in H3.
           eapply IHe; eassumption.
     ** rewrite negb_true_iff in H0.
        pose proof H1 as Hforallb. (* need this later *)
        rewrite forallb_forall in H1.
        rewrite forallb_forall in H2.

        eapply JPV_LetRecJP.
        -- assumption.
        -- intros v rhs HIn.
           specialize (H1 (v,rhs) HIn).
           apply H1.
        -- intros v rhs a HIn HJI.
           specialize (H1 (v,rhs) HIn).
           simpl in H1.
           rewrite isJoinId_eq in H1.
           specialize (H2 (v,rhs) HIn). simpl in H2.
           unfold isJoinPointsValidPair,  isJoinPointsValidPair_aux in *.
           rewrite HJI in *.
           rewrite Hforallb in *.
           destruct (Z.eqb_spec a 0).
           ++ eapply GJR_RHS; try assumption.
              eapply H; eassumption.
           ++ eapply H; eassumption.
        -- rewrite Hforallb in *.
           apply IHe; assumption.
 * destruct HiJPV.
   constructor.
   + eapply IHe; eassumption.
   + intros dc pats rhs Hin.
     rewrite forallb_forall in H1.
     specialize (H1 (dc, pats, rhs) Hin). simpl in H0.
     eapply H; eassumption.
 * constructor; intuition.
 * constructor; intuition.
 * constructor; intuition.
 * constructor; intuition.
Qed.
