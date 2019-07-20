(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Psatz.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import SetoidList.
Require Import Coq.Logic.ProofIrrelevance.

Require Import GHC.Base.

Require Import Proofs.Prelude.

Require Import CoreFVs.
Require Import Id.
Require Import Core.
Require UniqFM.

Require Import Proofs.Base.
Require Import Proofs.Axioms.
Require Import Proofs.ContainerAxioms.
Require Import Proofs.GhcTactics.
Require Import Proofs.Unique.
Require Import Proofs.Var.
Require Import Proofs.VarSetFSet.
Require Import Proofs.VarSet.

Open Scope Z_scope.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(** ** [StrongSubset] *)


(* A strong subset doesn't just have a subset of the uniques, but 
     also requires that the variables in common be almostEqual. *)
Definition StrongSubset (vs1 : VarSet) (vs2: VarSet) := 
  forall var, match lookupVarSet vs1 var with 
           | Some v =>  match lookupVarSet vs2 var with
                          | Some v' => almostEqual v v'
                          | None => False
                       end
           | None => True 
         end.


Notation "s1 {<=} s2" := (StrongSubset s1 s2) (at level 70, no associativity).
Definition StrongEquivalence s1 s2 := (StrongSubset s1 s2 /\ StrongSubset s2 s1).
Notation "s1 {=} s2" := (StrongEquivalence s1 s2)  (at level 70, no associativity).


Lemma StrongSubset_refl : forall vs, 
    StrongSubset vs vs.
Proof.
  unfold StrongSubset.
  move=> vs var.
  elim h: (lookupVarSet vs var) => //.
  eapply almostEqual_refl.
Qed.

Instance StrongSubset_Reflexive : Reflexive StrongSubset := StrongSubset_refl.

Lemma StrongSubset_trans : forall vs1 vs2 vs3, 
    StrongSubset vs1 vs2 -> StrongSubset vs2 vs3 -> StrongSubset vs1 vs3.
Proof.
  move => vs1 vs2 vs3 h1 h2 var.
  specialize (h1 var).
  specialize (h2 var).
  move: h1 h2.
  elim p1: (lookupVarSet vs1 var) => //;
  elim p2: (lookupVarSet vs2 var) => //;
  elim p3: (lookupVarSet vs3 var) => //.
  eapply almostEqual_trans.
Qed.


Instance StrongSubset_Transitive : Transitive StrongSubset := StrongSubset_trans.

Instance StrongSubset_Equivalence : Equivalence StrongEquivalence.
Proof.
  split; unfold Reflexive, Symmetric, Transitive, StrongEquivalence.
  - intros. split; reflexivity.
  - move=> x y [h1 h2]. eauto.
  - move=> x y z [h1 h2] [h3 h4].
    eauto using StrongSubset_trans.
Defined.  

Lemma StrongSubset_implies_Subset :
  forall vs1 vs2 , vs1 {<=} vs2 -> vs1 [<=] vs2.
Proof. 
  intros vs1 vs2.
  unfold StrongSubset, Subset.
  intros SS var IN.
  unfold In in *.
  specialize (SS var). 
  destruct (lookupVarSet vs1 var) eqn:VS1;
  destruct (lookupVarSet vs2 var) eqn:VS2; try contradiction.
  - apply lookupVarSet_elemVarSet in VS2.   
    auto.
  - apply elemVarSet_lookupVarSet in IN. destruct IN.
    rewrite VS1 in H. discriminate.
  - apply elemVarSet_lookupVarSet in IN. destruct IN.
    rewrite VS1 in H. discriminate.
Qed.

Lemma StrongEquivalence_implies_Equal :
  forall vs1 vs2 , vs1 {=} vs2 -> vs1 [=] vs2.
Proof. 
  intros vs1 vs2 [S1 S2].
  eapply subset_antisym;
  eauto using StrongSubset_implies_Subset.
Qed.

Lemma StrongSubset_extend_fresh :
  forall vs v, lookupVarSet vs v = None -> vs {<=} (extendVarSet vs v).
Proof.
  intros.
  unfold StrongSubset.
  intros var.
  destruct (var == v) eqn:EQV.
  rewrite -> lookupVarSet_eq with (v2 := v); auto.
  rewrite H. auto.
  destruct (lookupVarSet vs var) eqn:Lvar; auto.
  rewrite lookupVarSet_extendVarSet_neq.
  rewrite Lvar.
  apply almostEqual_refl.
  unfold CoreBndr in *. intro h. rewrite Base.Eq_sym in h. rewrite h in EQV. discriminate.
Qed.


Lemma StrongSubset_extendList_fresh :
  forall vs vs2,
  disjointVarSet vs (mkVarSet vs2) -> vs {<=} (extendVarSetList vs vs2).
Proof.
  intros.
  unfold StrongSubset.
  intros v.
  destruct_match; try trivial.
  case in2: (Foldable.elem v vs2).  
  * eapply elemNegbDisjoint in in2; eauto.
    eapply lookupVarSet_elemVarSet in Heq; eauto. 
    erewrite Heq in in2. done.
  * rewrite lookupVarSet_extendVarSetList_false; try done.
    rewrite Heq.
    eapply almostEqual_refl.
    rewrite in2. done.
Qed.


Lemma StrongSubset_extend_ae :
  forall vs1 vs2 v1 v2,
  vs1 {<=} vs2 -> almostEqual v1 v2 ->  (extendVarSet vs1 v1) {<=} (extendVarSet vs2 v2).
Proof.
  intros.
  unfold StrongSubset in *.
  intro var.
  destruct (v1 == var) eqn:EQv.
  rewrite lookupVarSet_extendVarSet_eq; auto.  
  rewrite lookupVarSet_extendVarSet_eq.
  assumption.
  apply almostEqual_eq in H0. eapply Eq_trans; try eassumption; try symmetry; assumption.
  rewrite lookupVarSet_extendVarSet_neq; auto.
  rewrite lookupVarSet_extendVarSet_neq; auto.
  eapply H.
  rewrite <- not_true_iff_false in EQv. contradict EQv.
  apply almostEqual_eq in H0. eapply Eq_trans; try eassumption; try symmetry; assumption.
  rewrite not_true_iff_false. assumption.
Qed.

Instance extendVarSet_ae_m :
  Proper (StrongSubset ==> almostEqual ==> StrongSubset) extendVarSet.
Proof. move=> x1 y1 E1 x2 y2 E2.  eapply StrongSubset_extend_ae; eauto. Qed.


Lemma StrongSubset_extend :
  forall vs1 vs2 v,
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSet vs1 v) (extendVarSet vs2 v).
Proof.
  intros.
  apply StrongSubset_extend_ae.
  * assumption.
  * apply almostEqual_refl.
Qed.

Lemma StrongSubset_extendVarSetList_ae :
  forall l1 l2 vs1 vs2,
  Forall2 almostEqual l1 l2 ->
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSetList vs1 l1) (extendVarSetList vs2 l2).
Proof.
  intros.
  revert vs1 vs2 H0. induction H; intros.
  * apply H0.
  * rewrite extendVarSetList_cons.
    apply IHForall2.
    apply StrongSubset_extend_ae; assumption.
Qed.

Instance extendVarSetList_ae_m :
  Proper (StrongSubset ==> (Forall2 almostEqual) ==> StrongSubset) extendVarSetList.
Proof. move=> x1 y1 E1 x2 y2 E2.  eapply StrongSubset_extendVarSetList_ae; eauto. Qed.



Lemma StrongSubset_extendVarSetList :
  forall l vs1 vs2,
  StrongSubset vs1 vs2 ->
  StrongSubset (extendVarSetList vs1 l) (extendVarSetList vs2 l).
Proof.
  intros.
  apply StrongSubset_extendVarSetList_ae; only 2: assumption.
  apply Forall2_diag.
  rewrite Forall_forall. intros. apply almostEqual_refl.
Qed.

Lemma StrongSubset_delVarSet :
  forall vs1 vs2 v,
  StrongSubset vs1 vs2 ->
  StrongSubset (delVarSet vs1 v) (delVarSet vs2 v).
Proof.
  intros.
  unfold StrongSubset in *.
  intro var.
  specialize (H var).
  destruct (v == var) eqn:EQv.
  - rewrite Base.Eq_sym in EQv.
    erewrite lookupVarSet_eq;
      [|eassumption].
    rewrite lookupVarSet_delVarSet_None.
    trivial.
  - rewrite lookupVarSet_delVarSet_neq;
      [|rewrite EQv; auto].
    destruct (lookupVarSet vs1 var) eqn:Hl; auto.
    rewrite lookupVarSet_delVarSet_neq;
      [|rewrite EQv; auto].
    auto.
Qed.


Instance delVarSet_ae_m :
  Proper (StrongSubset ==> almostEqual ==> StrongSubset) delVarSet.
Proof.
  move=> x1 y1 E1 x2 y2 E2.
  unfold StrongSubset in *.
  move=>var. specialize (E1 var).
  destruct (x2 == var) eqn:EQv.
  - rewrite Base.Eq_sym in EQv.
    erewrite lookupVarSet_eq;
      [|eassumption].
    rewrite lookupVarSet_delVarSet_None.
    trivial.
  - rewrite lookupVarSet_delVarSet_neq;
      [|rewrite EQv; auto].
    destruct (lookupVarSet x1 var) eqn:Hl; auto.
    rewrite -> E2 in EQv.
    rewrite lookupVarSet_delVarSet_neq;
      [|rewrite EQv; auto].
    auto.
Qed.  


Lemma StrongSubset_delete_fresh :
  forall vs v,
  lookupVarSet vs v = None ->
  StrongSubset vs (delVarSet vs v).
Proof.
  intros.
  unfold StrongSubset in *.
  intro var.
  destruct (v == var) eqn:EQv.
  - rewrite Base.Eq_sym in EQv.
    erewrite lookupVarSet_eq;
      [|eassumption].
    rewrite H.
    trivial.
  - rewrite lookupVarSet_delVarSet_neq;
      [|rewrite EQv; auto].
    destruct (lookupVarSet vs var) eqn:Hl; auto.
    apply almostEqual_refl.
Qed.

Lemma StrongSubset_delVarSetList:
  forall vs1 vs2 vs,
  StrongSubset vs1 vs2 ->
  StrongSubset (delVarSetList vs1 vs) (delVarSetList vs2 vs).
Proof.
  intros vs1 vs2 vs.
  generalize dependent vs2.
  generalize dependent vs1.
  induction vs;
    intros vs1 vs2 H; hs_simpl;
      [assumption|].
  eapply StrongSubset_delVarSet in H.
  eauto.
Qed.

Instance delVarSetList_ae_m :
  Proper (StrongSubset ==> Forall2 almostEqual ==> StrongSubset) delVarSetList.
Proof.
  move=> vs1 vs2 E1 xs1 xs2 E2.
  generalize dependent vs2.
  generalize dependent vs1.
  induction E2;
    move=> vs1 vs2 SS; hs_simpl; [assumption|].
  eapply IHE2.
  rewrite -> SS.
  rewrite -> H. 
  reflexivity.
Qed.  

(* Respects_StrongSubset *)

Definition Respects_StrongSubset (P : VarSet -> Prop) : Prop :=
  forall (vs1 vs2 : VarSet),
  vs1 {<=} vs2 -> P vs1 -> P vs2.
Existing Class Respects_StrongSubset.

Require Import Coq.Classes.Morphisms.
Global Instance Respects_StrongSubset_iff_morphism:
  Proper (pointwise_relation VarSet iff ==> iff) Respects_StrongSubset.
Proof.
  intros ???.
  split; intros ?????;
  unfold pointwise_relation in H;
  firstorder.
Qed.

Lemma Respects_StrongSubset_const:
  forall P, Respects_StrongSubset (fun _ => P).
Proof. intros ?????. assumption. Qed.

Lemma Respects_StrongSubset_and:
  forall P Q,
    Respects_StrongSubset P ->
    Respects_StrongSubset Q ->
    Respects_StrongSubset (fun x => P x /\ Q x).
Proof.
  unfold Respects_StrongSubset in *.
  intros ????????.
  firstorder.
Qed.

Lemma Respects_StrongSubset_andb:
  forall (P Q : VarSet -> bool),
    Respects_StrongSubset (fun x => P x = true) ->
    Respects_StrongSubset (fun x => Q x = true) ->
    Respects_StrongSubset (fun x => P x && Q x = true).
Proof.
  unfold Respects_StrongSubset in *.
  intros ????????.
  simpl_bool.
  firstorder.
Qed.


Lemma Respects_StrongSubset_forall:
  forall a (xs : list a) P,
    Forall (fun x => Respects_StrongSubset (fun vs => P vs x)) xs ->
    Respects_StrongSubset (fun vs => Forall (P vs) xs).
Proof.
  unfold Respects_StrongSubset in *.
  intros.
  rewrite -> Forall_forall in *.
  firstorder.
Qed.

Lemma Respects_StrongSubset_forallb:
  forall a (xs : list a) P,
    Forall (fun x => Respects_StrongSubset (fun vs => P vs x = true)) xs ->
    Respects_StrongSubset (fun vs => forallb (P vs) xs = true).
Proof.
  unfold Respects_StrongSubset in *.
  intros.
  rewrite -> forallb_forall in *.
  rewrite -> Forall_forall in *.
  firstorder.
Qed.


Lemma Respects_StrongSubset_elemVarSet:
  forall v,
  Respects_StrongSubset (fun vs => elemVarSet v vs = true).
Proof.
  intros ????.
  simpl_bool; intuition.
  apply StrongSubset_implies_Subset in H.
  set_b_iff; fsetdec.
Qed.

Lemma Respects_StrongSubset_delVarSet:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (delVarSet vs v)).
Proof.
  intros v P H vs1 vs2 Hs Hvs1.
  apply StrongSubset_delVarSet with (v:=v) in Hs.
  unfold Respects_StrongSubset in H.  
  apply H in Hs; auto.
Qed.

Lemma Respects_StrongSubset_delVarSetList:
  forall vs2 P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (delVarSetList vs vs2)).
Proof.
  intros vs2 P H vs vs' Hs Hvs2.
  apply StrongSubset_delVarSetList with (vs:=vs2) in Hs.
  unfold Respects_StrongSubset in H.  
  apply H in Hs; auto.
Qed.


Lemma Respects_StrongSubset_extendVarSet:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSet vs v)).
Proof.
  intros v P H vs vs' Hs Hvs.
  apply StrongSubset_extend with (v:=v) in Hs.
  unfold Respects_StrongSubset in H.
  apply H in Hs; auto.
Qed.


Lemma Respects_StrongSubset_extendVarSetList:
  forall vs' P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (extendVarSetList vs vs')).
Proof.
  intros vs P H vs1 vs2 Hs Hvs1.
  eapply StrongSubset_extendVarSetList with (l:=vs) in Hs.
  unfold Respects_StrongSubset in H.
  apply H in Hs; auto.
Qed. 

Lemma StrongSubset_filterVarSet: 
  forall f1 f2 vs,
    RespectsVar f1 -> RespectsVar f2 ->
  (forall v, f1 v = true  -> f2 v = true) ->
  filterVarSet f1 vs {<=} filterVarSet f2 vs.
Proof.
  intros.
  unfold StrongSubset.
  intros var.
  destruct (f1 var) eqn:Heq1.
  - rewrite lookupVarSet_filterVarSet_true; auto.
    destruct (lookupVarSet vs var) eqn:Hl; [|trivial].
    rewrite lookupVarSet_filterVarSet_true; auto.
    rewrite Hl.
    apply almostEqual_refl.
  - rewrite lookupVarSet_filterVarSet_false; auto.
Qed.

(* Is this weakening? *)
Lemma weaken:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall {vs1} {vs2},
  StrongSubset vs1 vs2 ->
  P vs1 -> P vs2.
Proof. intros. unfold Respects_StrongSubset in R. eapply R; eassumption. Qed.

Lemma weakenb:
  forall {P : VarSet -> bool} {R : Respects_StrongSubset (fun x => P x )},
  forall {vs1} {vs2},
  StrongSubset vs1 vs2 ->
  P vs1  -> P vs2 .
Proof. intros. unfold Respects_StrongSubset in R. eapply R; eassumption. Qed.

Lemma Respects_StrongSubset_extendVarSet_ae:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall vs v1 v2,
  almostEqual v1 v2 ->
  P (extendVarSet vs v1) <-> P (extendVarSet vs v2).
Proof.
  intros.
  split; apply R; (apply StrongSubset_extend_ae;
    [ reflexivity | assumption + (apply almostEqual_sym; assumption) ]).
Qed.


Lemma Respects_StrongSubset_extendVarSetList_ae:
  forall {P : VarSet -> Prop} {R : Respects_StrongSubset P},
  forall vs vs1 vs2,
  Forall2 almostEqual vs1 vs2 ->
  P (extendVarSetList vs vs1) <-> P (extendVarSetList vs vs2).
Proof.
  split; apply R; apply StrongSubset_extendVarSetList_ae.
  * assumption.
  * reflexivity.
  * clear -H.
    induction H; constructor.
    + apply almostEqual_sym; assumption.
    + assumption.
  * reflexivity.
Qed.

Lemma StrongSubset_extendVarSet_fresh : 
  forall vs var, lookupVarSet vs var = None ->
            StrongSubset vs (extendVarSet vs var).
Proof.
  apply StrongSubset_extend_fresh.
Qed.

Lemma StrongSubset_extendVarSetList_fresh : 
  forall vs vars, freshList vars vs ->
             StrongSubset vs (extendVarSetList vs vars).
Proof.
  intros.
  apply StrongSubset_extendList_fresh.
  apply disjointVarSet_mkVarSet.
  induction vars; auto.
  apply freshList_cons in H as [H1 H2].
  apply Forall_cons; auto.
  apply lookupVarSet_None_elemVarSet.
  assumption.
Qed.
