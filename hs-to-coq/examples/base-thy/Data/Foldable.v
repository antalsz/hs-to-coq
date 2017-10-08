Require Import GHC.Base.
Require Import Data.Foldable.

Require Import Proofs.GHC.Base.

(* -------------------------------------------------------------------- *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.

Theorem hs_coq_foldr_list {A B} (f : A -> B -> B) (z : B) (l : list A) :
  foldr f z l = Coq.Lists.List.fold_right f z l.
Proof. rewrite hs_coq_foldr_base. auto. Qed.

Class FoldableLaws {t} `{Foldable t} := {
(*  foldr_foldMap : forall f z t, foldr f z t = appEndo (foldMap (Mk_Endo ∘ f) t ) z;
  foldl_foldMap : forall f z t,
     foldl f z t = appEndo (getDual (foldMap (Mk_Dual ∘ Mk_Endo ∘ flip f) t)) z;
  foldMap_id : forall a `{Monoid a}, @fold t _ a = foldMap id *)
}.

Class FoldableFunctor {t} `{Foldable t} `{Functor t} := {
  foldfmap : forall a b (f : a -> b)`{Monoid b}, foldMap f = fold ∘ fmap f;
}.