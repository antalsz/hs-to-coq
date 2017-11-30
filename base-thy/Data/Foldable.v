Require Import GHC.Base.
Require Import Data.Foldable.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

Require Import mathcomp.ssreflect.ssreflect.
Set Bullet Behavior "Strict Subproofs".

(* -------------------------------------------------------------------- *)

(* Laws *)

Class FoldableLaws {t} `{Foldable t} := {
(*  foldr_foldMap : forall f z t, foldr f z t = appEndo (foldMap (Mk_Endo ∘ f) t ) z;
  foldl_foldMap : forall f z t,
     foldl f z t = appEndo (getDual (foldMap (Mk_Dual ∘ Mk_Endo ∘ flip f) t)) z;
  foldMap_id : forall a `{Monoid a}, @fold t _ a = foldMap id *)
}.

Class FoldableFunctor {t} `{Foldable t} `{Functor t} := {
  foldfmap : forall a b (f : a -> b)`{Monoid b}, foldMap f = fold ∘ fmap f;
}.

(* -------------------------------------------------------------------- *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Theorem hs_coq_length_list {A} (l : list A) :
  length l = Zlength l.
Proof. apply hs_coq_list_length. Qed.

Theorem hs_coq_length_list' {A} (l : list A) :
  Data.Foldable.instance_Data_Foldable_Foldable_list_length l = Zlength l.
Proof. apply hs_coq_length_list. Qed.

Theorem hs_coq_foldr_list {A B} (f : A -> B -> B) (z : B) (l : list A) :
  foldr f z l = Coq.Lists.List.fold_right f z l.
Proof. by rewrite ->hs_coq_foldr_base. Qed.

Theorem hs_coq_foldr_list' {A B} (f : A -> B -> B) (z : B) (l : list A) :
  Data.Foldable.instance_Data_Foldable_Foldable_list_foldr f z l = Coq.Lists.List.fold_right f z l.
Proof. apply hs_coq_foldr_list. Qed.

Theorem hs_coq_foldl_list {A B} (f : B -> A -> B) (z : B) (l : list A) :
  foldl f z l = Coq.Lists.List.fold_left f l z.
Proof. apply hs_coq_foldl_base. Qed.

Theorem hs_coq_foldl_list' {A B} (f : B -> A -> B) (z : B) (l : list A) :
  Data.Foldable.instance_Data_Foldable_Foldable_list_foldl f z l = Coq.Lists.List.fold_left f l z.
Proof. apply hs_coq_foldl_list. Qed.
