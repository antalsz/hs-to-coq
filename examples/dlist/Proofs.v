From mathcomp Require Import ssreflect ssrfun.
Set Bullet Behavior "Strict Subproofs".

Require Import GHC.Base.
Require Import GHC.List Proofs.GHC.List.
Require Import DList.

Import ListNotations.

Arguments "∘" {_} _ _ _ /.

(** Well-formed [DList]s *)

Import GHC.Base.Notations.

Definition fromList {a} : list a -> DList a :=
  MkDList GHC.Base.∘ Coq.Init.Datatypes.app.

Definition equiv {A} (dxs dys : DList A) : Prop := fromDList dxs =1 fromDList dys.
Arguments equiv {_} !_ / _.
Infix "=dl" := equiv (at level 70).
  
Definition Denotes {A} (dxs : DList A) (lxs : list A) : Prop :=
  dxs =dl fromList lxs.
Arguments Denotes {_} !_ / _.

Definition WF {A} (dxs : DList A) : Prop :=
  exists lxs : list A, Denotes dxs lxs.

(** Proving that [DList] functions preserve [Denotes]/[WF] *)

Ltac Denotes_to_WF f_Denotes :=
  repeat intros [? ?]; eexists; apply f_Denotes; eassumption.

(** [fromList] *)

Theorem fromList_Denotes {A} (lxs : list A) :
  Denotes (fromList lxs) lxs.
Proof. done. Qed.

Theorem fromList_WF {A} (lxs : list A) :
  WF (fromList lxs).
Proof. Denotes_to_WF @fromList_Denotes. Qed.

(** [empty] *)

Theorem empty_Denotes {A} :
  Denotes (@empty A) [].
Proof. done. Qed.

Theorem empty_WF {A} :
  WF (@empty A).
Proof. Denotes_to_WF @empty_Denotes. Qed.

(** [singleton] *)

Theorem singleton_Denotes {A} (x : A) :
  Denotes (singleton x) [x].
Proof. done. Qed.

Theorem singleton_WF {A} (x : A) :
  WF (singleton x).
Proof. Denotes_to_WF @singleton_Denotes. Qed.

(** [cons] *)

Theorem cons__Denotes {A} (x : A) (dxs : DList A) (lxs : list A) :
  Denotes dxs lxs ->
  Denotes (cons_ x dxs) (x :: lxs).
Proof.
  move: dxs => [fxs] /= den_xs ys.
  by rewrite den_xs.
Qed.

Theorem cons__WF {A} (x : A) (dxs : DList A) :
  WF dxs ->
  WF (cons_ x dxs).
Proof. Denotes_to_WF @cons__Denotes. Qed.

(** [append] *)

Theorem append_Denotes {A} (dxs : DList A) (lxs : list A)
                           (dys : DList A) (lys : list A) :
  Denotes dxs lxs ->
  Denotes dys lys ->
  Denotes (append dxs dys) (lxs ++ lys).
Proof.
  move: dxs dys => [fxs] [fys] /= den_xs den_ys zs.
  by rewrite den_xs den_ys app_assoc.
Qed.

Theorem append_WF {A} (dxs dys : DList A) :
  WF dxs ->
  WF dys ->
  WF (append dxs dys).
Proof. Denotes_to_WF @append_Denotes. Qed.

(** [toList] *)

Theorem Denotes_toList {A} (dxs : DList A) (lxs : list A) :
  Denotes dxs lxs ->
  toList dxs = lxs.
Proof.
  move: dxs => [fxs] /= den_xs.
  by rewrite den_xs app_nil_r.
Qed.

Theorem WF_toList {A} (dxs : DList A) :
  WF dxs ->
  Denotes dxs (toList dxs).
Proof. by intros [lxs den_xs]; rewrite (Denotes_toList _ lxs). Qed.

(** Compositional theorems *)

Theorem fromList_cons__empty {A} (lxs : list A) :
  fromList lxs = foldr cons_ empty lxs.
Proof.
  rewrite /fromList /=; elim: lxs => [|x lxs IH] //=.
  by rewrite -IH /=.
Qed.

Theorem fromList_toList {A} (dxs : DList A) :
  WF dxs ->
  fromList (toList dxs) =dl dxs.
Proof.
  case: dxs => [fxs] /= [/= lxs den_xs] ys /=.
  by rewrite !den_xs app_nil_r.
Qed.

Theorem toList_fromList {A} (lxs : list A) :
  toList (fromList lxs) = lxs.
Proof.
  by rewrite /= app_nil_r.
Qed.

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
  length (toList (append dxs dys)) = length (toList (append dys dxs)).
Proof.
  move: dxs dys => [fxs] [fys] /= [/= lxs den_xs] [/= lys den_ys].
  by rewrite !den_xs !den_ys
             !hs_coq_list_length !Zlength_correct
             !app_length /= !Nat.add_0_r Nat.add_comm.
Qed.
