From mathcomp Require Import ssreflect ssrfun.
Set Bullet Behavior "Strict Subproofs".

Require Import GHC.Base.
Require Import GHC.List Proofs.GHC.List.
Require Import DList.

Import ListNotations.

Arguments "∘" {_} _ _ _ /.

(** Well-formed [DList]s *)

Import GHC.Base.Notations.

Definition equiv {A} (dxs dys : DList A) : Prop := fromDList dxs =1 fromDList dys.
Arguments equiv {_} !_ / _.
Infix "=dl" := equiv (at level 70).

Notation "[ ]" := empty.
Notation "[ x ]" := (singleton x).
Notation "x ::: y" := (cons_ x y) (at level 60).
Notation "x +++ y" := (append x y) (at level 61).

Inductive Denotes {A} : DList A -> list A -> Prop :=
| emptyD : forall dxs,
    dxs =dl [] ->
    Denotes dxs []
| singletonD : forall dxs x,
    dxs =dl [x] ->
    Denotes dxs [x]
| consD : forall dxs lxs x dys,
    Denotes dxs lxs ->
    dys =dl x ::: dxs ->
    Denotes dys (x :: lxs)
| appendD : forall dxs lxs dys lys dzs,
    Denotes dxs lxs ->
    Denotes dys lys ->
    dzs =dl dxs +++ dys ->
    Denotes dzs (lxs ++ lys).

Hint Constructors Denotes.

Definition WF {A} (dxs: DList A) : Prop :=
  exists lxs, Denotes dxs lxs.

(** Proving that [DList] functions preserve [Denotes]/[WF] *)

Ltac prove_WF fdenotes:=
  rewrite /WF; repeat move=>[? ?]; eexists; eapply fdenotes; last done; eauto.

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
  all: repeat match goal with
              | [ds: DList _ |- _] =>
                destruct ds
              end.
  Focus 4.
  - rewrite /= /eqfun in H1.
    specialize (H1 lys0).
    simpl. rewrite H1 -app_assoc.
    simpl in IHDenotes1. simpl in IHDenotes2.
    specialize (IHDenotes2 lys0). rewrite IHDenotes2.
    apply IHDenotes1.
  all: repeat match goal with
              | [H: _ =dl _ |- _] =>
                rewrite /= /eqfun in H;
                  specialize (H lys)
              end.
  - done.
  - done.
  - simpl. rewrite H0. f_equal. apply IHDenotes.
Qed.

(** [reflect] *)

Definition reflect {A} : list A -> DList A :=
  MkDList GHC.Base.∘ Coq.Init.Datatypes.app.

Theorem reflect_Denotes {A} (dxs : DList A) (lxs : list A) :
  dxs =dl reflect lxs <-> Denotes dxs lxs.
Proof.
  split.
  - generalize dependent dxs.
    induction lxs.
    + by constructor.
    + intros. apply consD with (dxs0:=reflect lxs).
      * apply IHlxs. done.
      * done.
  - destruct dxs. rewrite /= /eqfun. intros. 
    eapply fromDList_Denotes with (lys:=x) in H.
    done.
Qed.

Theorem reflect_WF {A} (lxs : list A) :
  WF (reflect lxs).
Proof. rewrite /WF. exists lxs. eapply reflect_Denotes. done. Qed.

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

(** Compositional theorems *)

Theorem reflect_cons__empty {A} (lxs : list A) :
  reflect lxs = foldr cons_ empty lxs.
Proof.
  rewrite /reflect /=; elim: lxs => [|x lxs IH] //=.
  by rewrite -IH /=.
Qed.

Theorem reflect_reify {A} (dxs : DList A) :
  WF dxs ->
  reflect (reify dxs) =dl dxs.
Proof.
  inversion 1.
  eapply reify_P; eauto.
  apply fsym.
  by apply reflect_Denotes.
Qed. 
Theorem reify_reflect {A} (lxs : list A) :
  reify (reflect lxs) = lxs.
Proof.
  by rewrite /= app_nil_r.
Qed.

Notation "x 'in' y" := (In x (reify y)) (at level 61).
Notation "x =l y" := (reify x = reify y) (at level 62).

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

Theorem length_append_comm {A} (dxs dys : DList A) :
  WF dxs ->
  WF dys ->
  Datatypes.length (reify (append dxs dys)) = Datatypes.length (reify (append dys dxs)).
Proof.
  intros. inversion H; inversion H0.
  eapply reify_P.
  - eapply appendD with (dxs0:=dxs)(dys0:=dys); eauto. done.
  - eapply reify_P.
    + eapply appendD with (dxs0:=dys)(dys0:=dxs); eauto. done.
    + rewrite !app_length. apply Nat.add_comm.
Qed.

Hint Resolve empty_WF.
Hint Resolve singleton_WF.
Hint Resolve cons__WF.
Hint Resolve append_WF.

Hint Resolve reify_Denotes.

(** Some theorems from [Coq.Lists.List]. *)
Section ListTheorems.
  Variable A : Type.
  Variable x : A.
  Variable l r : DList A.
  Context {WFl : WF l} {WFr : WF r}.

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
         by apply (singletonD _ x); try done
       | [ H: Denotes ?l ?x |- Denotes (cons_ ?a ?l) _] =>
         eapply (consD _ x a); [apply H | try done ]
       | [ |- Denotes (cons_ ?a ?l) _] =>
         eapply (consD _ (reify l) a); eauto
       | [ H1: Denotes ?x _, H2: Denotes ?y _ |- Denotes (append ?x ?y) _] =>
         eapply (appendD x _ y _); [apply H1 | apply H2 | try done]
       | [ |- Denotes (append ?x ?y) _] =>
         eapply (appendD x (reify x) y (reify y)); [auto | auto | try done]
       end | idtac]
    end; try solve [auto]; try done.

  Ltac solve_by_reify := repeat apply_reify.
  
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
    
  Theorem destruct_list :
    (exists x : A, exists tl : DList A, l =l x ::: tl) \/ (l =l []).
  Proof.
    inversion WFl.
    solve_by_reify.
    destruct x0; auto.
    left. exists a. exists (reflect x0).
    eapply reify_P with (lxs:=a :: x0); [| done].
    eapply consD with (dxs:=reflect x0).
    - apply reflect_Denotes. done.
    - done.
  Qed.
End ListTheorems.
