Require Import Omega.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.
Local Open Scope Z_scope.


Require Import BitUtils.
Require Import DyadicIntervals.
Require Import Tactics.

(** * The IntMap formalization *)

Require Import GHC.DeferredFix.
Require Import IntSetProofs.
Require Import Data.IntSet.Internal.
Require Import Data.IntMap.Internal.

Axiom deferredFix2_eq : forall a b r `{Default r} (f : (a -> b -> r) -> (a -> b -> r)),
  deferredFix2 f = f (deferredFix2 f).

(** ** Well-formed IntMap.

This section introduces the predicate to describe the well-formedness of
an IntMap. It has parameters that describe the range that this map covers,
and a function that carries it denotation. This way, invariant preservation
and functional correctness of an operation can be expressed in one go.
*)

Definition singletonRange k : range := (k, 0%N).


Inductive Desc : forall {a}, IntMap a -> range -> (Z -> option a) -> Prop :=
  | DescTip : forall a k (v : a) r f,
    (forall i, f i = if i =? k then Some v else None) ->
    r = singletonRange k ->
    Desc (Tip k v) r f
  | DescBin : forall a m1 r1 f1 m2 r2 f2 p msk r (f : Z  -> option a),
    Desc m1 r1 f1 ->
    Desc m2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r -> 
    (forall i, f i = oro (f1 i) (f2 i)) ->
    Desc (Bin p msk m1 m2) r f.

(** A variant that also allows [Nil], or sets that do not
    cover the full given range, but are certainly contained in them.
    This is used to describe operations that may delete elements.
 *)

Inductive Desc0 : forall {a}, IntMap a -> range -> (Z -> option a) -> Prop :=
  | Desc0Nil : forall {a} r (f : Z -> option a), (forall i, f i = None) -> Desc0 Nil r f
  | Desc0NotNil :
      forall {a},
      forall m r f r' (f' : Z -> option a),
      forall (HD : Desc m r f),
      forall (Hsubrange: isSubrange r r' = true)
      (Hf : forall i, f' i = f i),
      Desc0 m r' f'.

(** A variant that also allows [Nil] and does not reqiure a range. Used
    for the top-level specification.
 *)

Inductive Sem : forall {a}, IntMap a -> (Z -> option a) -> Prop :=
  | SemNil : forall {a} (f : Z -> option a), (forall i, f i = None) -> Sem Nil f
  | DescSem : forall {a} s r (f : Z -> option a) (HD : Desc s r f), Sem s f.

(** The highest level: Just well-formedness.
 *)

Definition WF {a} (s : IntMap a) : Prop := exists f, Sem s f.

Lemma Desc0_Sem:
  forall a (m : IntMap a) r f, Desc0 m r f -> Sem m f.
Proof.
  intros.
  destruct H.
  * apply SemNil; eassumption.
  * eapply DescSem. admit.
Admitted.


(** * Specifying [restrictKeys] *)

(* We can extract the argument to [deferredFix] from the definition of [restrictKeys]. *)

Definition restrictKeys_f {a} :
  (IntMap a -> IntSet -> IntMap a) -> (IntMap a -> IntSet -> IntMap a).
Proof.
  let rhs := eval unfold restrictKeys in (@restrictKeys a) in
  match rhs with context[ deferredFix2 ?f ] => exact f end.
Defined.


Definition restrictKeys_body {a} := restrictKeys_f (@restrictKeys a). 

Lemma restrictKeys_eq {a} (m : IntMap a) s :
  restrictKeys m s = restrictKeys_body m s.
Proof.
  enough (@restrictKeys a = restrictKeys_body) by congruence.
  apply deferredFix2_eq.
Qed.

Definition restrictBitMapToRange r bm :=
  let p := rPrefix r in
  let msk := rMask r in 
    N.land (N.land bm (N.lxor (bitmapOf p - Z.to_N 1)%N (N.ones 64%N)))
           (N.lor (bitmapOf (Z.lor p (Z.lor msk (msk - 1))))
           (bitmapOf (Z.lor p (Z.lor msk (msk - 1))) - Z.to_N 1)%N).

Lemma Desc0_subRange:
  forall {a} {m : IntMap a} {r r' f}, Desc0 m r f -> isSubrange r r' = true -> Desc0 m r' f.
Proof.
  intros.
  induction H.
  * apply Desc0Nil; assumption.
  * eapply Desc0NotNil; try eassumption.
    isSubrange_true.
Qed.

Lemma Desc_inside:
 forall {a m r f i} {v:a}, Desc m r f -> f i = Some v -> inRange i r = true.
Admitted.

Lemma bin_Desc0:
  forall a (m1 : IntMap a) r1 f1 m2 r2 f2 p msk r f,
    Desc0 m1 r1 f1 ->
    Desc0 m2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r -> 
    (forall i, f i = oro (f1 i) (f2 i)) ->
    Desc0 (bin p msk m1 m2) r f.
Admitted.

Ltac point_to_inRange_Map :=
  lazymatch goal with 
    | [ HD : IntSetProofs.Desc ?s ?r ?f, Hf : ?f ?i = true |- _ ] 
      => apply (IntSetProofs.Desc_inside HD) in Hf
    | [ H : bitmapInRange ?r ?bm ?i = true |- _ ]
      => apply bitmapInRange_inside in H
    | [ HD : Desc ?m ?r ?f, Hf : ?f ?i = Some _ |- _ ] 
      => apply (Desc_inside HD) in Hf
  end.
  
Ltac solve_f_eq_disjoint_Map :=
  solve_f_eq;
  repeat point_to_inRange_Map;
  repeat saturate_inRange;
  try inRange_disjoint. (* Only try this, so that we see wher we are stuck. *)


Program Fixpoint restrictKeys_Desc
  a (m1 : IntMap a) r1 f1 s2 r2 f2 f
  { measure (size_nat m1 + Data.IntSet.Internal.size_nat s2) } :
  Desc m1 r1 f1 ->
  IntSetProofs.Desc s2 r2 f2 ->
  (forall i, f i = if f2 i then f1 i else None) ->
  Desc0 (restrictKeys m1 s2) r1 f 
  := fun HD1 HD2 Hf => _.
Next Obligation.
  rewrite restrictKeys_eq.
  unfold restrictKeys_body, restrictKeys_f.
  unfoldMethods.

  destruct HD1.
  * (* m1 is a Tip *)
    subst.
    erewrite member_Desc by eassumption.
    destruct (f2 k) eqn: Hf2.
    + eapply Desc0NotNil; try (apply isSubrange_refl); try (intro; reflexivity).
      eapply DescTip; try reflexivity.
      intro i.
      rewrite Hf, H; clear Hf H.
      destruct (Z.eqb_spec i k).
      - subst. rewrite Hf2. reflexivity.
      - destruct (f2 i); reflexivity.
    + apply Desc0Nil.
      intro i.
      rewrite Hf, H; clear Hf H.
      destruct (Z.eqb_spec i k).
      - subst. rewrite Hf2. reflexivity.
      - destruct (f2 i); reflexivity.

  * (* m1 is a Bin *)
    inversion HD2.
    + (* s2 is a Tip *)
      clear restrictKeys_Desc. subst.
      set (m := Bin (rPrefix r) (rMask r) m1 m2) in *.
      change (Desc0 (restrictBM (restrictBitMapToRange r bm) (lookupPrefix (rPrefix r2) m)) r f).
      admit.
    + (* s2 is also a Bin *)
      subst.
      set (m := Bin (rPrefix r) (rMask r) m1 m2) in *.
      set (s := IntSet.Internal.Bin (rPrefix r2) (rMask r2) s1 s0) in *.
      rewrite !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r)).
      ++ (* s2 is smaller than m1 *)
        apply nomatch_zero_smaller; try assumption; intros.
        - (* s2 is disjoint of s1 *)
          apply Desc0Nil.
          solve_f_eq_disjoint_Map.

        - (* s2 is part of the left half of m1 *)
          eapply Desc0_subRange.
          eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
          ** subst m s. simpl. omega.
          ** solve_f_eq_disjoint_Map.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
        - (* s2 is part of the right half of m1 *)
          eapply Desc0_subRange.
          eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
          ** subst m s. simpl. omega.
          ** solve_f_eq_disjoint_Map.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.

      ++ (* s2 is not smaller than m1 *)
        destruct (N.ltb_spec (rBits r) (rBits r2)).
        -- (* s2 is smaller than m1 *)
          apply nomatch_zero_smaller; try assumption; intros.
          - (* m1 is disjoint of s2 *)
            apply Desc0Nil.
            solve_f_eq_disjoint_Map.
          - (* s1 is part of the left half of s2 *)
            eapply Desc0_subRange.
            eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
            ** subst m s. simpl. omega.
            ** eapply DescBin; try beassumption; reflexivity.
            ** solve_f_eq_disjoint_Map.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.

          - (* s1 is part of the right half of s2 *)

            eapply Desc0_subRange.
            eapply restrictKeys_Desc; clear restrictKeys_Desc; try eassumption.
            ** subst s m. simpl. omega.
            ** eapply DescBin; try beassumption; reflexivity.
            ** solve_f_eq_disjoint_Map.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.

        -- (* s1 and s2 are the same size *)
          apply same_size_compare; try Nomega; intros.
          - subst.
            eapply bin_Desc0; try assumption; try reflexivity.
            ** eapply restrictKeys_Desc.
               --- subst s m. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ** eapply restrictKeys_Desc.
               --- subst s m. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.
            ** solve_f_eq_disjoint_Map.
          - apply Desc0Nil.
            solve_f_eq_disjoint_Map.
Admitted.

Lemma restrictKeys_Sem:
  forall a (m1 : IntMap a) f1 s2 f2,
  Sem m1 f1 ->
  IntSetProofs.Sem s2 f2 ->
  Sem (restrictKeys m1 s2) (fun i => if f2 i then f1 i else None).
Proof.
  intros.
  destruct H; [|destruct H0].
  * rewrite restrictKeys_eq.
    apply SemNil. solve_f_eq.
  * replace (restrictKeys s IntSet.Internal.Nil) with (@Nil a) by (rewrite restrictKeys_eq; destruct s; reflexivity).
    apply SemNil. solve_f_eq.
  * eapply Desc0_Sem. eapply restrictKeys_Desc; try eauto.
Qed.

Lemma restrictKeys_WF:
  forall a (m1 : IntMap a) s2, WF m1 -> IntSetProofs.WF s2 -> WF (restrictKeys m1 s2).
Proof.
  intros.
  destruct H, H0.
  eexists. apply restrictKeys_Sem; eassumption.
Qed.