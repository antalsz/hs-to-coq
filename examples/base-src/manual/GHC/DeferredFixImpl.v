(** * Deferred fix *)

(**
This file shows that the axioms in [GHC.DeferredFix] follow from classical choice
and fuctional extensionality.*)

Definition recurses {a b} (R : a -> a -> Prop) (f : (a -> b) -> (a -> b)) :=
    forall g h x, (forall y, R y x -> g y = h y) -> f g x = f h x.

Definition recurses_on {a b} (P : a -> Prop) (R : a -> a -> Prop) (f : (a -> b) -> (a -> b)) :=
  forall g h x, P x -> (forall y, P y ->  R y x -> g y = h y) -> f g x = f h x.

(**
We want to justify these axioms:

  Axiom deferredFix: forall {a r}, r -> ((a -> r) -> (a -> r)) -> a -> r.
 
  Axiom deferredFix_eq_on: forall {a b} (d : b) (f : (a -> b) -> (a -> b)) (P : a -> Prop) (R : a -> a -> Prop),
     well_founded R -> recurses_on P R f ->
     forall x, P x -> deferredFix d f x = f (deferredFix d f) x.
*)

Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Wellfounded.Wellfounded.

Definition constructFixpoint :forall {a b} (d : b)
  (F : (a -> b) -> (a -> b))
  (R : a -> a -> Prop),
 well_founded R -> a -> b.
Proof.
  intros ????? Hwf.
  refine (Fix Hwf _ _).
  intros x f'.
  refine (F _ x).
  intro y.
  case (excluded_middle_informative (R y x)).
  * apply f'.
  * intro. exact d.
Defined.

Lemma constructFixpoint_eq : forall {a b} (d : b)
  (F : (a -> b) -> (a -> b))
  (R : a -> a -> Prop)
  (HWf : well_founded R)
  (P : a -> Prop)
  (Hterm : recurses_on P R F),
  forall x, P x ->
  constructFixpoint d F R HWf x = F (constructFixpoint d F R HWf) x.
Proof.
  intros.
  unfold constructFixpoint.
  rewrite Fix_eq.
  - apply Hterm; only 1: assumption.
    intros y Py Ryx.
    destruct (excluded_middle_informative _).
    * reflexivity.
    * contradict n. assumption.
  - intros.
    f_equal.
    extensionality y.
    destruct (excluded_middle_informative _).
    * apply H0.
    * reflexivity.
Qed.

Lemma constructFixpoint_eq_iff : forall {a b} (d : b)
  (F : (a -> b) -> (a -> b))
  (R : a -> a -> Prop)
  (HWf : well_founded R)
  (P : a -> Prop)
  (Hterm : recurses_on P R F),
  forall f,
  (forall x, P x -> F f x = f x) ->
  forall x, P x -> constructFixpoint d F R HWf x = f x.
Proof.
  intros.
  pose proof (HWf x).
  induction H1.
  rewrite <- H by assumption.
  rewrite @constructFixpoint_eq with (P := P) by assumption.
  apply Hterm; only 1: assumption.
  intuition.
Qed.

Lemma construct_fixpoint_sub : forall {a b} (d : b)
  (F : (a -> b) -> (a -> b))
  (R : a -> a -> Prop)
  (HWf : well_founded R)
  (P : a -> Prop)
  (Hterm : recurses_on P R F)
  (R' : a -> a -> Prop)
  (HWf' : well_founded R')
  (P' : a -> Prop)
  (Hterm' : recurses_on P' R' F)
  (HsubR : forall x y, R' x y -> R x y)
  (HsubP : forall x, P' x -> P x),
  forall y, P' y ->
  constructFixpoint d F R HWf y = constructFixpoint d F R' HWf' y.
Proof.
  intros.
  pose proof (HWf' y) as HAcc.
  induction HAcc.
  assert (P x) by intuition.
  erewrite @constructFixpoint_eq by eassumption.
  erewrite @constructFixpoint_eq by eassumption.
  apply Hterm'; only 1: assumption.
  intros y HPy HRy.
  apply H1; assumption.
Qed.

Lemma recurses_on_intersection: forall {a b} (d : b)
  (F : (a -> b) -> (a -> b))
  (R : a -> a -> Prop)
  (P : a -> Prop)
  (Hterm : recurses_on P R F)
  (R' : a -> a -> Prop)
  (P' : a -> Prop)
  (Hterm' : recurses_on P' R' F),
  let P'' := fun x => P x /\ P' x in
  let R'' := fun x y => R x y /\ R' x y in
  recurses_on P'' R'' F.
Proof.
  intros.
  intros g h x [Px P'x] Heq.
  set (gh := fun y => if excluded_middle_informative (P y /\ R y x) then g y else h y).
  transitivity (F gh x).
  * apply Hterm; only 1: assumption.
    intros. unfold gh.
    destruct (excluded_middle_informative _); try reflexivity.
    apply Heq; tauto.
  * apply Hterm'; only 1: assumption.
    intros. unfold gh.
    destruct (excluded_middle_informative _); try reflexivity.
    apply Heq; unfold R'', P'' in *; tauto.
Qed.

Lemma construct_fixpoint_ext : forall {a b} (d : b)
  (F : (a -> b) -> (a -> b))
  (R : a -> a -> Prop)
  (HWf : well_founded R)
  (P : a -> Prop)
  (Hterm : recurses_on P R F)
  (R' : a -> a -> Prop)
  (HWf' : well_founded R')
  (P' : a -> Prop)
  (Hterm' : recurses_on P' R' F),
  forall y, P y -> P' y ->
  constructFixpoint d F R HWf y = constructFixpoint d F R' HWf' y.
Proof.
  intros.
  set (P'' := fun x => P x /\ P' x).
  set (R'' := fun x y => R x y /\ R' x y).
  assert (Hterm'' : recurses_on P'' R'' F) 
    by (eapply recurses_on_intersection; eassumption).
  assert (HWf'' : well_founded R''). {
    apply wf_incl with (R2 := R).
    * intros ???. unfold R'' in *; intuition.
    * assumption.
  }
  etransitivity.
  * eapply @construct_fixpoint_sub with (HWf' := HWf'').
    - apply Hterm.
    - apply Hterm''.
    - intros. unfold R'' in *. intuition.
    - intros. unfold P'' in *. intuition.
    - unfold P'' in *. intuition.
  * symmetry.
    eapply @construct_fixpoint_sub with (HWf' := HWf'').
    - apply Hterm'.
    - apply Hterm''.
    - intros. unfold R'' in *. intuition.
    - intros. unfold P'' in *. intuition.
    - unfold P'' in *. intuition.
Qed.

Definition deferredFix: forall {a r}, r -> ((a -> r) -> (a -> r)) -> a -> r.
Proof.
  intros ?? d F x.
  case (excluded_middle_informative (
    (exists P, P x /\ (exists R, well_founded R /\ recurses_on P R F))
  )); intro H.
  * apply constructive_indefinite_description in H.
    destruct H as [P [HPx HR]].
    apply constructive_indefinite_description in HR.
    destruct HR as [R [HWf Hterm]].
    exact (constructFixpoint d F R HWf x).
  * exact d.
Defined.


Lemma deferredFix_eq_on: forall {a b} (d : b) (F : (a -> b) -> (a -> b)) (P : a -> Prop) (R : a -> a -> Prop),
   well_founded R -> recurses_on P R F ->
   forall x, P x -> deferredFix d F x = F (deferredFix d F) x.
Proof.
  intros ?????? HWf Hterm x Px.
  unfold deferredFix.
  destruct (excluded_middle_informative _) as [H|H].
  * destruct (constructive_indefinite_description _) as [P' [HP'x HexR']].
    destruct (constructive_indefinite_description _) as [R' [HWf' Hterm']].
    erewrite @constructFixpoint_eq with (P := P') by assumption.
    apply Hterm'; only 1: assumption.
    intros y P'y R'y.
    destruct (excluded_middle_informative _) as [H'|H'].
    - destruct (constructive_indefinite_description _) as [P'' [HP''x HexR'']].
      destruct (constructive_indefinite_description _) as [R'' [HWf'' Hterm'']].
      apply @construct_fixpoint_ext with (P := P') (P' := P''); assumption.
    - contradict H'.
      exists P'.
      split; try assumption.
  * contradict H.
    exists P.
    split; try assumption.
    exists R. split; assumption.
Qed.
