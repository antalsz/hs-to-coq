(** This file has been manually derived from UniqSet.hs, with modifications in support of 
    the UniqSet invariant. *)

(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require GHC.Base.
Require GHC.Prim.
Require UniqFM.
Require Unique.
Import GHC.Base.Notations.
Import GHC.Base.ManualNotations.

Import Unique.
Import UniqFM.
Import GHC.Base.

(* Converted type declarations: *)

Require Proofs.GHC.List.
Require Proofs.Data.Foldable.
Require Import Data.IntMap.Internal.


Require Import Proofs.ContainerAxioms.
Require Import Proofs.Unique.


(* Properties about Uniques that we need. *)

Lemma lookup_delFromUFM:
  forall A (H: Uniquable A) z (s : UniqFM A) (x y: A),
   (lookupUFM s x = Some y ->
       getUnique x = getUnique y) ->
      lookupUFM (delFromUFM s z) x = Some y ->
      getUnique x = getUnique y.
Proof.
  intros A H z s x y Hu.
  unfold lookupUFM in *.
  destruct s; unfold delFromUFM in *.
  destruct (eqUnique (getUnique z) (getUnique x)) eqn:EQ.
  - apply eqUnique_eq in EQ. rewrite <- EQ in *.
    rewrite delete_eq.
    intro C. inversion C.
  - apply eqUnique_neq in EQ.
    intro L.
    rewrite delete_neq in L.
    + apply (Hu L).
    + unfold getWordKey.
      unfold getKey.
      unfold not in *.
      intro h.
      apply EQ.
      destruct (getUnique x).
      destruct (getUnique z).
      subst.
      auto.
Qed.

Lemma lookup_fold_left_app_delFromUFM:
  forall {A} {H: Uniquable A} (s : UniqFM A) (x y: A) (zs: list A),
    (lookupUFM s x = Some y ->
     getUnique x = getUnique y) ->
    lookupUFM (fold_left delFromUFM zs s) x = Some y ->
    getUnique x = getUnique y.
Proof.
  intros A H s x y zs.
  revert s.
  induction zs as [ | z zs']; intros s.
  - rewrite List.List_foldl_foldr.
    unfold Datatypes.id.
    simpl.
    intros.
    auto.
  - simpl.
    intros Hl Hf.
    apply (IHzs' (delFromUFM s z)); [|auto].
    apply lookup_delFromUFM.
    auto.
Qed.

Lemma lookup_delFromUFM_Directly:
  forall A (H: Uniquable A) z (s : UniqFM A) (x y: A),
   (lookupUFM s x = Some y ->
       getUnique x = getUnique y) ->
      lookupUFM (delFromUFM_Directly s z) x = Some y ->
      getUnique x = getUnique y.
Proof.
  intros A H z s x y Hu.
  unfold lookupUFM in *.
  destruct s; unfold delFromUFM_Directly in *.
  destruct (eqUnique (getUnique x) z) eqn:EQ.
  - apply eqUnique_eq in EQ. rewrite <- EQ in *.
    rewrite delete_eq.
    intro C. inversion C.
  - apply eqUnique_neq in EQ.
    intro L.
    rewrite delete_neq in L.
    + apply (Hu L).
    + unfold getWordKey.
      unfold getKey.
      unfold not in *.
      destruct (getUnique x).
      destruct z as [n'].
      intros Hg.
      apply EQ.
      f_equal.
      assumption.
Qed.

Lemma lookup_fold_left_app_delFromUFM_Directly:
  forall {A} {H: Uniquable A} (s : UniqFM A) (x y: A)
    (zs: list Unique),
    (lookupUFM s x = Some y ->
     getUnique x = getUnique y) ->
    lookupUFM (fold_left delFromUFM_Directly zs s) x = Some y ->
    getUnique x = getUnique y.
Proof.
  intros A H s x y zs.
  revert s.
  induction zs as [ | z zs']; intros s.
  - rewrite List.List_foldl_foldr.
    unfold Datatypes.id.
    simpl.
    intros.
    auto.
  - simpl.
    intros Hl Hf.
    apply (IHzs' (delFromUFM s z)); [|auto].
    apply lookup_delFromUFM_Directly.
    auto.
Qed.

Lemma lookup_difference:
  forall A (H: Uniquable A) (i i' : IntMap A) (n:N) (y:A),
    (forall y, lookup n i = Some y -> MkUnique n = getUnique y) ->
    (forall y, lookup n i' = Some y -> MkUnique n = getUnique y) ->
    lookup n (difference i i') = Some y ->
    MkUnique n = getUnique y.
Proof.
  intros A H i i' n y Hi Hi' Hd.  
  destruct (lookup n i') eqn:Hli'.
  - erewrite lookup_difference_in_snd in Hd;
      [|eassumption].
    inversion Hd.
  - erewrite lookup_difference_not_in_snd in Hd;
      try eassumption.
    auto.
Qed.

(* -------------------------------------------------------------------- *)

(** The invariant is that for any unique, the result that we get out has 
    the same unique stored.
*)
Polymorphic Definition UniqInv@{i} {a:Type@{i}} (fm : UniqFM.UniqFM a) `{Unique.Uniquable a} : Type@{i} :=
  forall (x:a)(y:a), 
    UniqFM.lookupUFM fm x = Some y -> getUnique x = getUnique y. 


Polymorphic Definition UniqSet@{i} (a:Type@{i}) `{Unique.Uniquable a} : Type@{i} :=
  sigT (fun fm => UniqInv fm).

Local Notation Mk_UniqSet s:= (@existT _ _ s _).

Definition getUniqSet' {a}`{Uniquable a} (arg_0__ : UniqSet a) :=
  let 'existT _ getUniqSet' _ := arg_0__ in
  getUniqSet'.

(* Converted value declarations: *)

(* SCW we DON'T want to coerce *)
(*
Instance Unpeel_UniqSet ele
   : GHC.Prim.Unpeel (UniqSet ele) (UniqFM.UniqFM ele) :=
  GHC.Prim.Build_Unpeel _ _ (fun '(Mk_UniqSet y) => y) Mk_UniqSet.
*)

(* Skipping instance Eq___UniqSet *)

(* Skipping instance Outputable__UniqSet of class Outputable *)

(* SCW: Monoid instances added by hand. *)

Program Definition Monoid__UniqSet_mempty {inst_a} `{Uniquable inst_a} : UniqSet inst_a :=
  Mk_UniqSet GHC.Base.mempty.

Program Definition Semigroup__UniqSet_op_zlzlzgzg__ {inst_a}`{Unique.Uniquable inst_a}
   : UniqSet inst_a -> UniqSet inst_a -> UniqSet inst_a :=
  fun m1 m2 => Mk_UniqSet (plusUFM (getUniqSet' m1) (getUniqSet' m2)).
Next Obligation.
  destruct m1. destruct m2.
  simpl.
  unfold UniqInv in *. 
  intros y1 y2 Hu.
  unfold lookupUFM, plusUFM in *.
  destruct x. destruct x0.
  rewrite <- lookup_union in Hu.
  destruct Hu as [Hl |[_ Hr]].
  eauto.
  eauto.
Qed.

Program Instance Semigroup__UniqSet {a}`{Unique.Uniquable a} : GHC.Base.Semigroup (UniqSet a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__UniqSet_op_zlzlzgzg__ |}.

Local Definition Monoid__UniqSet_mappend {inst_a}`{Unique.Uniquable inst_a}
   : UniqSet inst_a -> UniqSet inst_a -> UniqSet inst_a :=
  Semigroup__UniqSet_op_zlzlzgzg__ .

Local Definition Monoid__UniqSet_mconcat {inst_a}`{Unique.Uniquable inst_a}
  : list (UniqSet inst_a) -> UniqSet inst_a :=
  GHC.Base.foldr Monoid__UniqSet_mappend Monoid__UniqSet_mempty.

Program Instance Monoid__UniqSet {a}`{Unique.Uniquable a} : GHC.Base.Monoid (UniqSet a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__UniqSet_mappend ;
         GHC.Base.mconcat__ := Monoid__UniqSet_mconcat ;
         GHC.Base.mempty__ := Monoid__UniqSet_mempty |}.

(* Skipping instance Data__UniqSet of class Data *)

Program Definition addOneToUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet set, x => Mk_UniqSet (UniqFM.addToUFM set x x) 
    end.
Next Obligation.
unfold UniqInv in *.
unfold UniqFM.addToUFM.
unfold UniqFM.lookupUFM in *.
intros.
destruct set.
rename arg_1__ into z.
destruct (eqUnique (getUnique z) (getUnique x)) eqn:EQ.
- apply eqUnique_eq in EQ. rewrite <- EQ in *.
  rewrite lookup_insert in H0.
  inversion H0.
  auto.
- apply eqUnique_neq in EQ.
  rewrite lookup_insert_neq in H0.
  apply wildcard'.
  auto.
  unfold getWordKey.
  unfold getKey.
  unfold not in *.
  intro h.
  apply EQ.
  destruct (getUnique x).
  destruct (getUnique z).
  subst.
  auto.
Defined.

Definition addListToUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  Data.Foldable.foldl' addOneToUniqSet.

Program Definition delListFromUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> list a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, l => Mk_UniqSet (UniqFM.delListFromUFM s l)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x y.
  specialize (wildcard' x y).
  unfold delListFromUFM in *.
  rewrite Foldable.hs_coq_foldl_list.
  apply lookup_fold_left_app_delFromUFM.
  assumption.
Qed.

Program Definition delListFromUniqSet_Directly {a} `{Unique.Uniquable a}
   : UniqSet a -> list Unique.Unique -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, l => Mk_UniqSet (UniqFM.delListFromUFM_Directly s l)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x y.
  specialize (wildcard' x y).
  unfold delListFromUFM_Directly in *.
  rewrite Foldable.hs_coq_foldl_list.
  apply lookup_fold_left_app_delFromUFM_Directly.
  assumption.
Qed.
                                        
Program Definition delOneFromUniqSet {a} `{Unique.Uniquable a}
   : UniqSet a -> a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, a => Mk_UniqSet (UniqFM.delFromUFM s a)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x y.
  specialize (wildcard' x y).
  apply lookup_delFromUFM.
  assumption.
Defined.

Program Definition delOneFromUniqSet_Directly {a} `{Unique.Uniquable a}
   : UniqSet a -> Unique.Unique -> UniqSet a :=
  fun x y =>
    match x, y with
    | Mk_UniqSet s, u => Mk_UniqSet (UniqFM.delFromUFM_Directly s u)
    end.

Program Definition delOneFromUniqSet_Directly {a} `{Unique.Uniquable a}
   : UniqSet a -> Unique.Unique -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, u => Mk_UniqSet (UniqFM.delFromUFM_Directly s u)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x y.
  specialize (wildcard' x y).
  apply lookup_delFromUFM_Directly.
  assumption.
Qed.

Definition elemUniqSet_Directly {a} `{Unique.Uniquable a} : Unique.Unique -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_UniqSet s => UniqFM.elemUFM_Directly a s 
    end.

Definition elementOfUniqSet {a} `{Unique.Uniquable a}
   : a -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, Mk_UniqSet s => UniqFM.elemUFM a s
    end.

Program Definition emptyUniqSet {a} `{Unique.Uniquable a}: UniqSet a :=
  Mk_UniqSet UniqFM.emptyUFM.

Definition mkUniqSet {a} `{Unique.Uniquable a} : list a -> UniqSet a :=
  Data.Foldable.foldl' addOneToUniqSet emptyUniqSet.

Program Definition filterUniqSet {a} `{Unique.Uniquable a} : (a -> bool) -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => Mk_UniqSet (UniqFM.filterUFM p s)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x y.
  unfold lookupUFM, filterUFM in *. unfold IntMap.Internal.filter.
  destruct s.
  intro h.
  apply wildcard'.
  eapply lookup_filterWithKey.
  eauto.
Defined.

Program Definition filterUniqSet_Directly {elt} `{Unique.Uniquable elt}
   : (Unique.Unique -> elt -> bool) -> UniqSet elt -> UniqSet elt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_UniqSet s => Mk_UniqSet (UniqFM.filterUFM_Directly f s)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x y.
  unfold lookupUFM, filterUFM_Directly in *.
  destruct s.
  intro h.
  apply wildcard'.
  eapply lookup_filterWithKey.
  eauto.
Defined.

Definition getUniqSet {a} `{Unique.Uniquable a} : UniqSet a -> UniqFM.UniqFM a :=
  getUniqSet'.

Program Definition intersectUniqSets {a} `{Unique.Uniquable a} : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => Mk_UniqSet (UniqFM.intersectUFM s t)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x y.
  unfold lookupUFM, intersectUFM in *.
  destruct s. destruct t.
  intro h.
  eapply lookup_intersection in h. destruct h.
  eauto.
Defined.

Definition isEmptyUniqSet {a} `{Unique.Uniquable a} : UniqSet a -> bool :=
  fun '(Mk_UniqSet s) => UniqFM.isNullUFM s.

Definition lookupUniqSet {a} {b} `{Unique.Uniquable a} `{Unique.Uniquable b}
   : UniqSet b -> a -> option b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, k => UniqFM.lookupUFM s k
    end.

Definition lookupUniqSet_Directly {a} `{Unique.Uniquable a}
   : UniqSet a -> Unique.Unique -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, k => UniqFM.lookupUFM_Directly s k
    end.

Program Definition minusUniqSet {a} `{Unique.Uniquable a} : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => Mk_UniqSet (UniqFM.minusUFM s t)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x y.
  unfold lookupUFM, minusUFM in *.
  destruct s. destruct t.
  unfold getWordKey in *.
  unfold getKey in *.
  specialize (wildcard'0 x).
  specialize (wildcard' x).
  destruct (getUnique x) in *.
  apply lookup_difference; auto.
Qed.

Definition nonDetEltsUniqSet {elt} `{Unique.Uniquable elt} : UniqSet elt -> list elt :=
  UniqFM.nonDetEltsUFM GHC.Base.∘ getUniqSet'.

Definition mapUniqSet {b} {a} `{Unique.Uniquable a} `{Unique.Uniquable b}
   : (a -> b) -> UniqSet a -> UniqSet b :=
  fun f => mkUniqSet GHC.Base.∘ (GHC.Base.map f GHC.Base.∘ nonDetEltsUniqSet).

Definition nonDetFoldUniqSet {elt} {a} `{Unique.Uniquable elt}
   : (elt -> a -> a) -> a -> UniqSet elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | c, n, Mk_UniqSet s => UniqFM.nonDetFoldUFM c n s
    end.

Definition nonDetFoldUniqSet_Directly {elt} {a} `{Unique.Uniquable elt} `{Unique.Uniquable a}
   : (Unique.Unique -> elt -> a -> a) -> a -> UniqSet elt -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, n, Mk_UniqSet s => UniqFM.nonDetFoldUFM_Directly f n s
    end.

Definition nonDetKeysUniqSet {elt} `{Unique.Uniquable elt} : UniqSet elt -> list Unique.Unique :=
  UniqFM.nonDetKeysUFM GHC.Base.∘ getUniqSet'.

Program Definition partitionUniqSet {a} `{Unique.Uniquable a}
   : (a -> bool) -> UniqSet a -> (UniqSet a * UniqSet a)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, existT _ s _ => let '(x,y):= (UniqFM.partitionUFM p s) in (existT _ x _, existT _ y _)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x' y' Hl.
  apply wildcard'.
  destruct x as [m'].
  destruct s as [m].
  eapply lookup_partition; eauto.
Defined.
Next Obligation.
  unfold UniqInv in *.
  intros x' y' Hl.
  apply wildcard'.
  destruct y as [m'].
  destruct s as [m].  
  eapply lookup_partition; eauto.
Defined.

Program Definition restrictUniqSetToUFM {a} {b} `{Unique.Uniquable a} `{Unique.Uniquable b}
   : UniqSet a -> UniqFM.UniqFM b -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, m => Mk_UniqSet (UniqFM.intersectUFM s m)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x' y'.
  unfold lookupUFM, intersectUFM in *.
  destruct s.
  destruct arg_1__.
  intro h.
  rewrite <- lookup_intersection in h. destruct h.
  eauto.
Defined.

Definition sizeUniqSet {a} `{Unique.Uniquable a} : UniqSet a -> nat :=
  fun '(Mk_UniqSet s) => UniqFM.sizeUFM s.

Program Definition unionUniqSets {a} `{Unique.Uniquable a} : UniqSet a -> UniqSet a -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_UniqSet s, Mk_UniqSet t => Mk_UniqSet (UniqFM.plusUFM s t)
    end.
Next Obligation.
  unfold UniqInv in *.
  intros x y.
  unfold lookupUFM, plusUFM in *.
  destruct s. destruct t.
  intro h.
  rewrite <- lookup_union in h.
  destruct h as [h | [h1 h2]]; auto.
Qed.

Definition unionManyUniqSets {a} `{Unique.Uniquable a} (xs : list (UniqSet a)) : UniqSet a :=
  match xs with
  | nil => emptyUniqSet
  | cons set sets => Data.Foldable.foldr unionUniqSets set sets
  end.

Definition uniqSetAll {a} `{Unique.Uniquable a} : (a -> bool) -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, Mk_UniqSet s => UniqFM.allUFM p s
    end.

Definition uniqSetAny {a} `{Unique.Uniquable a} : (a -> bool) -> UniqSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, existT _ s _ => UniqFM.anyUFM p s
    end.

(*
Program Definition uniqSetMinusUFM {a} {b} `{Unique.Uniquable a} `{Unique.Uniquable b}
   : UniqSet a -> UniqFM.UniqFM b -> UniqSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | existT _ s _, t => Mk_UniqSet (UniqFM.minusUFM s t) _
    end.
Next Obligation.
Admitted. *)

Program Definition unitUniqSet {a} `{Unique.Uniquable a} : a -> UniqSet a :=
  fun x => Mk_UniqSet (UniqFM.unitUFM x x).
Next Obligation.
  unfold UniqInv.
  intros x0 y.
  unfold lookupUFM, unitUFM.
  unfold singleton.
  simpl.
  destruct (_GHC.Base.==_ (getWordKey (getUnique x0)) (getWordKey (getUnique x))) eqn:EQ.
  unfold Internal.Key, Num.Word in *.
  rewrite EQ.
  intro h. inversion h. subst.
  apply eq_getWordKey. auto.
  unfold Internal.Key, Num.Word in *.
  rewrite EQ.
  intro h. inversion h.
Defined.

(* Definition unsafeUFMToUniqSet {a} : UniqFM.UniqFM a -> UniqSet a :=
  Mk_UniqSet. *)

(* External variables:
     bool cons list nat op_zt__ option Data.Foldable.foldl' Data.Foldable.foldr
     GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.map GHC.Base.mappend
     GHC.Base.mappend__ GHC.Base.mconcat GHC.Base.mconcat__ GHC.Base.mempty
     GHC.Base.mempty__ GHC.Base.op_z2218U__ GHC.Base.op_zlzlzgzg__
     GHC.Base.op_zlzlzgzg____ GHC.Prim.Build_Unpeel GHC.Prim.Unpeel GHC.Prim.coerce
     UniqFM.UniqFM UniqFM.addToUFM UniqFM.allUFM UniqFM.anyUFM UniqFM.delFromUFM
     UniqFM.delFromUFM_Directly UniqFM.delListFromUFM UniqFM.delListFromUFM_Directly
     UniqFM.elemUFM UniqFM.elemUFM_Directly UniqFM.emptyUFM UniqFM.filterUFM
     UniqFM.filterUFM_Directly UniqFM.intersectUFM UniqFM.isNullUFM UniqFM.lookupUFM
     UniqFM.lookupUFM_Directly UniqFM.minusUFM UniqFM.nonDetEltsUFM
     UniqFM.nonDetFoldUFM UniqFM.nonDetFoldUFM_Directly UniqFM.nonDetKeysUFM
     UniqFM.partitionUFM UniqFM.plusUFM UniqFM.sizeUFM UniqFM.unitUFM
     Unique.Uniquable Unique.Unique
*)
