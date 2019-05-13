Require Import GHC.Base.
Require Import Data.Traversable.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

From Coq Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".



(** [mapAccumL] instance for lists *)

(*
-- |The 'mapAccumL' function behaves like a combination of 'fmap'
-- and 'foldl'; it applies a function to each element of a structure,
-- passing an accumulating parameter from left to right, and returning
-- a final value of this accumulator together with the new structure.
mapAccumL :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)
mapAccumL f s t = runStateL (traverse (StateL . flip f) t) s *)

(* 
mapAccumL               :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumL f s []        =  (s, [])
mapAccumL f s (x:xs)    =  (s'',y:ys)
                           where (s', y ) = f s x
                                 (s'',ys) = mapAccumL f s' xs
*)




Lemma mapAccumL_nil : forall a b c  (f : a -> b -> (a * c)) (s : a), 
   Traversable.mapAccumL f s nil = (s, nil).
Proof.
  intros a b c f s.
  unfold Traversable.mapAccumL.
  unfold Traversable.traverse,Traversable.Traversable__list, 
         Traversable.traverse__ , 
         Traversable.Traversable__list_traverse.
  simpl.
  auto.
Qed.

Lemma mapAccumL_cons : forall a b c x (xs : list b) (f : a -> b -> (a * c)) (s : a), 
   Traversable.mapAccumL f s (cons x xs) = 
   let '(s',y) := f s x in
   let '(s'',ys) := Traversable.mapAccumL f s' xs in
   (s'', cons y ys).
Proof.
  intros a b c x xs f s.
  unfold Traversable.mapAccumL.
  unfold Traversable.traverse,Traversable.Traversable__list, 
         Traversable.traverse__ , 
         Traversable.Traversable__list_traverse.
  rewrite Base.hs_coq_foldr_base.
  unfold op_z2218U__.
  simpl.
  unfold Utils.runStateL,liftA2, liftA2__, 
  Utils.Applicative__StateL,Utils.Applicative__StateL_liftA2,
  pure,pure__,Utils.Applicative__StateL_pure in *.
  destruct (fold_right
        (fun (x0 : b) (ys : Utils.StateL a (list c)) =>
         match ys with
         | Utils.Mk_StateL ky =>
             Utils.Mk_StateL
               (fun s0 : a =>
                let
                '(s', x1) := flip f x0 s0 in
                 let '(s'', y) := ky s' in (s'', x1 :: y))
         end) (Utils.Mk_StateL (fun s0 : a => (s0, nil))) xs) eqn:EQ.
  unfold flip.
  auto.
Qed.


Lemma forM_map:
  forall (m : Type -> Type) (a b c : Type) `{Monad m}
  (xs : list a) (act : b -> m c) (f : a -> b),
  Traversable.forM (map f xs) act = Traversable.forM xs (fun x => act (f x)).
Proof.
  intros.
  induction xs.
  * reflexivity.
  * cbv. f_equal. apply IHxs.
Qed.

Lemma forM_cong:
  forall {a m b} `{Monad m} (f g : a -> m b) (xs : list a),
  (forall x, In x xs -> f x = g x) ->
  Traversable.forM xs f = Traversable.forM xs g.
Proof.
  intros.
  rewrite <- forM_map with (act := fun x => x) (f := f).
  rewrite <- forM_map with (act := fun x => x) (f := g).
  f_equal.
  apply map_ext_in.
  assumption.
Qed.

