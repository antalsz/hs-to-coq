From mathcomp Require Import ssreflect ssrfun.
Set Bullet Behavior "Strict Subproofs".

Require Import GHC.Base.
Require Import GHC.List Proofs.GHC.List.
Require Import DList.

Import ListNotations.

Arguments "∘" {_} _ _ _ /.

(** Well-formed [DList]s *)

Import GHC.Base.Notations.

Notation "[ ]" := empty.
Notation "[ x ]" := (singleton x).
Notation "x ::: y" := (cons_ x y) (at level 60).
Notation "x +++ y" := (append x y) (at level 61).

Inductive Denotes {A} : DList A -> list A -> Prop :=
| emptyD :
    Denotes [] []
| singletonD : forall x,
    Denotes [x] [x]
| consD : forall dxs lxs x,
    Denotes dxs lxs ->
    Denotes (x ::: dxs) (x :: lxs)
| appendD : forall dxs lxs dys lys,
    Denotes dxs lxs ->
    Denotes dys lys ->
    Denotes (dxs +++ dys) (lxs ++ lys).

Hint Constructors Denotes.

Definition WF {A} (dxs: DList A) : Prop :=
  exists lxs, Denotes dxs lxs.

(** Proving that [DList] functions preserve [Denotes]/[WF] *)

Ltac prove_WF fdenotes:=
  rewrite /WF; repeat move=>[? ?]; eexists; eapply fdenotes; eauto.

Theorem empty_WF {A} :
  WF (@empty A).
Proof. prove_WF (@emptyD A). Qed.

(** [singleton] *)

Theorem singleton_WF {A} (x : A) :
  WF (singleton x).
Proof. prove_WF (@singletonD A). Qed.

(** [cons] *)

Theorem cons__WF {A} (x : A) (dxs : DList A) :
  WF dxs ->
  WF (cons_ x dxs).
Proof. prove_WF (@consD A). Qed.

(** [append] *)

Theorem append_WF {A} (dxs dys : DList A) :
  WF dxs ->
  WF dys ->
  WF (dxs +++ dys).
Proof. prove_WF (@appendD A). Qed.

(** [fromDList] *)

Theorem fromDList_Denotes {A} (dxs : DList A) (lxs lys : list A) :
  Denotes dxs lxs ->
  fromDList dxs lys = lxs ++ lys.
Proof.
  intro H. generalize dependent lys. induction H; intros.
  - reflexivity.
  - reflexivity.
  - destruct dxs. simpl in *. f_equal. apply IHDenotes.
  - destruct dxs; destruct dys. simpl in *.
    rewrite -app_assoc. specialize (IHDenotes1 (lys ++ lys0)).
    rewrite -IHDenotes1. f_equal. apply IHDenotes2.
Qed.

Theorem reflection {A} : forall lxs : list A,
    exists dxs, Denotes dxs lxs.
Proof.
  induction lxs.
  - exists []. constructor.
  - destruct IHlxs. exists (a ::: x). constructor; auto.
Qed.

(** [reify] *)

Definition reify {A} := @toList A.

Theorem Denotes_reify {A} (dxs : DList A) (lxs : list A) :
  Denotes dxs lxs -> reify dxs = lxs.
Proof.
  move=>H. destruct dxs. rewrite /reify /=.
  replace l with (fromDList (MkDList l)).
  replace lxs with (lxs ++ []).
  by apply fromDList_Denotes.
  by rewrite app_nil_r.
  done.
Qed.

Theorem reify_P {A} (dxs : DList A) (lxs : list A) (P : list A -> Prop) :
  Denotes dxs lxs -> P lxs -> P (reify dxs).
Proof.
  intros. apply Denotes_reify in H. by rewrite H.
Qed.

Theorem reify_Denotes {A} (dxs : DList A) (lxs : list A) :
  WF dxs ->
  reify dxs = lxs ->
  Denotes dxs lxs.
Proof.
  intros. rewrite -H0. inversion H.
  eapply reify_P. apply H1. done.
Qed.

Notation "x 'in' y" := (In x (reify y)) (at level 61).
Notation "x =l y" := (reify x = reify y) (at level 62).
Notation "'len' x" := (Datatypes.length (reify x)) (at level 61).

(** Tests *)

Theorem append_singletons {A} (x y : A) :
  toList (append (singleton x) (singleton y)) = [x; y].
Proof. done. Qed.

Theorem toList_cons_ {A} (x : A) (dxs : DList A) :
  toList (cons_ x dxs) = x :: toList dxs.
Proof. by move: dxs => [fxs] /=. Qed. 

Theorem appendA {A} :
  associative (@append A).
Proof. by move=> [fxs] [fys] [fzs] /=. Qed.

Hint Resolve empty_WF.
Hint Resolve singleton_WF.
Hint Resolve cons__WF.
Hint Resolve append_WF.

Hint Resolve reify_Denotes.

Ltac apply_reify :=
  match goal with
  | [ |- context[reify _]] =>
    eapply reify_P;
    [match goal with
     | [ H: Denotes ?x _ |- Denotes ?x _ ] =>
       apply H
     | [ |- Denotes empty _ ] =>
         by apply emptyD
     | [ |- Denotes (singleton ?x) _ ] =>
         by apply singletonD
     | [ H: Denotes ?l ?x |- Denotes (cons_ ?a ?l) _] =>
       eapply (consD _ x a); apply H 
     | [ |- Denotes (cons_ ?a ?l) _] =>
       eapply (consD _ (reify l) a); eauto
     | [ H1: Denotes ?x _, H2: Denotes ?y _ |- Denotes (append ?x ?y) _] =>
       eapply (appendD x _ y _); [apply H1 | apply H2 ]
     | [ |- Denotes (append ?x ?y) _] =>
       eapply (appendD x (reify x) y (reify y)); [auto | auto ]
     end | idtac]
  end; try solve [auto]; try done.

Ltac solve_by_reify := repeat apply_reify.

(** Some theorems from [Coq.Lists.List]. *)
Section ListTheorems.
  Variable A : Type.
  Variable x : A.
  Variable l r : DList A.
  Context {WFl : WF l} {WFr : WF r}.

  Theorem nil_cons : ~ ([] =l x ::: l).
  Proof. inversion WFl. solve_by_reify. Qed.
  
  Theorem in_eq : x in (x ::: l).
  Proof. inversion WFl. solve_by_reify. apply List.in_eq. Qed.

  Theorem app_comm_cons : x ::: (l +++ r) =l x ::: l +++ r.
  Proof. inversion WFl. inversion WFr. solve_by_reify. Qed.

  Theorem in_app_iff : x in (l +++ r) <-> x in l \/ x in r.
  Proof. inversion WFl; inversion WFr. solve_by_reify. apply List.in_app_iff. Qed.

  Theorem app_eq_unit :
    l +++ r =l [x] ->
    l =l [] /\ r =l [x] \/
    l =l [x] /\ r =l [].
  Proof. inversion WFl; inversion WFr. solve_by_reify. apply List.app_eq_unit. Qed.

  Theorem length_append_comm :
    len (l +++ r) = len (r +++ l).
  Proof.
    inversion WFl; inversion WFr.
    solve_by_reify. by rewrite !app_length Nat.add_comm.
  Qed.
    
  Theorem destruct_list :
    (exists x : A, exists tl : DList A, l =l x ::: tl) \/ (l =l []).
  Proof.
    inversion WFl.
    solve_by_reify.
    destruct x0; auto.
    left. exists a. pose proof (reflection x0). destruct H0. exists x1.
    solve_by_reify.
  Qed.
End ListTheorems.
