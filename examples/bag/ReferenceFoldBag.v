Require Import Bag.
Require Import Proofs.

Require Import Proofs.Data.Foldable.

Require Import ListUtils.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope program_scope.

From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Bullet Behavior "Strict Subproofs".

(* From Bag.hs:171-176, in the comments *)
Definition referenceFoldBag {r} {a} : (r -> r -> r) -> (a -> r) -> r -> Bag
                                      a -> r :=
  fix referenceFoldBag arg_27__ arg_28__ arg_29__ arg_30__
        := match arg_27__ , arg_28__ , arg_29__ , arg_30__ with
             | t , u , e , Mk_EmptyBag => e
             | t , u , e , (Mk_UnitBag x) => u x
             | t , u , e , (Mk_TwoBags b1 b2) => t (referenceFoldBag t u e b1)
                                                   (referenceFoldBag t u e b2)
             | t , u , e , (Mk_ListBag xs) => Coq.Lists.List.fold_right
                                              (Coq.Program.Basics.compose t u) e xs
           end.
(* Original:
foldBag t u e EmptyBag        = e
foldBag t u e (UnitBag x)     = u x
foldBag t u e (TwoBags b1 b2) = (foldBag t u e b1) `t` (foldBag t u e b2)
foldBag t u e (ListBag xs)    = foldr (t.u) e xs
*)

(* This equivalence requires that `t` be associative, which is documented, but
   also that `e` be the identity for `t`, which is *not*.  `foldBag` is only
   ever used twice in GHC, and in that case `e` is the identity, but there's a
   documentation/definition disagreement.  The ListBag case will always include
   `e`, so for the real implementation and the reference implementation to
   align, there must be a missing requirement that `e` be associative.  But that
   might be too strong of a requirement in the end! *)

Theorem referenceFoldBag_ok {A R} (f : R -> R -> R) (u : A -> R) (z : R) (b : Bag A) :
  associative f -> right_id z f -> left_id z f ->
  referenceFoldBag f u z b = fold_right f z (map u (bagToList b)).
Proof.
  move=> f_assoc z_right_id z_left_id.
  elim: b => [| x | l IHl r IHr | xs] //=.
  - by rewrite bagToList_TwoBags IHl IHr -fold_right_fold_right // map_app fold_right_app.
  - by rewrite bagToList_ListBag fold_right_map.
Qed.

Corollary foldBag_is_referenceFoldBag_if_id
          {A R} (f : R -> R -> R) (u : A -> R) (z : R) (b : Bag A) :
  associative f -> right_id z f -> left_id z f ->
  foldBag f u z b = referenceFoldBag f u z b.
Proof.
  move=> f_assoc z_right_id z_left_id.
  rewrite foldBag_ok // referenceFoldBag_ok //.
Qed.

Corollary foldBag_isn't_referenceFoldBag_unless_id
          {R} (f : R -> R -> R) (z : R) :
  associative f ->
  (exists x, f x z <> x) \/ (exists x, f z x <> x) ->
  exists {A} (u : A -> R) (b : Bag A),
    foldBag f u z b <> referenceFoldBag f u z b.
Proof.
  move=> f_assoc [[a z_not_right_id] | [a z_not_left_id]].
  - by exists unit, (fun _ => a), (Mk_UnitBag tt).
  - admit.
    (* Can we really prove this case?  Do we really need left_id in
       referenceFoldBag_ok, or is that an accident of our proof? *)
Abort.

Module BagNeedsUnit.

  Definition pure {A} (x : A) : list A := [x].

  Lemma same_empty_list' {A} (tail : list A) (b : Bag A) :
    foldBag app pure tail b = referenceFoldBag app pure [] b ++ tail.
  Proof.
    elim: b tail => [| x | l IHl r IHr | xs] //= tail.
    - by rewrite IHr IHl app_assoc.
    - by rewrite
         /Data.Foldable.foldr /Foldable.instance_Foldable_list /Data.Foldable.foldr__
         hs_coq_foldr_list' fold_right_cons fold_right_cons_nil.
  Qed.

  Lemma same_empty_list {A} (b : Bag A) :
    foldBag app pure [] b = referenceFoldBag app pure [] b.
  Proof. by rewrite same_empty_list' app_nil_r. Qed.
  
  Theorem counterexample {A} (x : A) (xs : list A) :
    exists b,
      well_formed_bag b /\
      foldBag app pure (x :: xs) b <> referenceFoldBag app pure (x :: xs) b.
  Proof. by exists (Mk_UnitBag x). Qed.

End BagNeedsUnit.
