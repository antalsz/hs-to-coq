Require Import Prelude.
Require Import Successors.
Require Import GHC.BaseThy.

(* We need a PreludeTheory for this sort of stuff. *)
Section list_proofs.

(*
  Definition list_fmap_const {a} {b} :  a -> list b -> list a :=
    map ∘ const.

  Instance list_functor : Functor list := {
                                           fmap := fun {a}{b} => map
                                         }.
  Proof.
    intros. exact (list_fmap_const X X0).
  Defined.

  Class FunctorLaws (t : Type -> Type) `{ Functor t } :=
    {
      map_id : forall a (x: t a), fmap id x = x;
      map_map : forall a b c (f : a -> b) (g : b -> c) (x : t a),
          fmap g (fmap f x) = fmap (g ∘ f) x
    }.


Lemma list_map_id:
  forall a (x : list a),
  map id x = x.
Proof.
  intros. induction x.
  * auto.
  * simpl. rewrite IHx. auto.
Qed.

Lemma list_map_map:
  forall a b c (f : a -> b) (g : b -> c) (x : list a),
  map g (map f x) = map (g ∘ f) x.
Proof.
  intros.
  unfold fmap, list_functor.
  induction x.
  * auto.
  * simpl. rewrite IHx. auto.
Qed.

Instance  list_functor_laws : FunctorLaws list := {
                                                 map_id := list_map_id;
                                                 map_map := list_map_map
                                               }.

*)
Lemma map_append:
  forall a b (f : a -> b) (x y : list a),
  map f (x ++ y) = map f x ++ map f y.
Proof.
  intros.
  intros.
  induction x.
  * auto.
  * simpl. rewrite IHx. auto.
Qed.

Lemma map_cong:
  forall a b (f g : a -> b) (x : list a),
  (forall x, f x = g x) -> map f x = map g x.
Proof.
  intros.
  induction x.
  * auto.
  * simpl. rewrite H. rewrite IHx. auto.
Qed.

(* This should be the list monoid, no? *)
Lemma append_nil:
  forall a (x : list a), app x nil = x.
Proof.
  intros.
  induction x.
  * auto.
  * simpl. rewrite IHx. auto.
Qed.

Lemma append_assoc:
  forall a (x y z : list a),
  app (app x y) z = app x (app y z).
Proof.
  intros.
  induction x.
  * auto.
  * simpl. rewrite IHx. auto.
Qed.

End list_proofs.

(* A tactic to rewrite with the list functor *)
Ltac rewrite_Functor_list :=
  let K := fresh in
  let L := fresh in
  pose (K := @functor_identity list instance_Functor_list instance_FunctorLaws_list); clearbody K;
  pose (L := @functor_composition list instance_Functor_list instance_FunctorLaws_list); clearbody L;
  try rewrite K; try rewrite L;
  unfold fmap, instance_Functor_list, BaseGen.instance_Functor_list_fmap in K, L;
  try rewrite K; try rewrite L;
  clear K; clear L.



Lemma functor_law_1:
  forall a (x : Succs a),
  fmap id x = x.
Proof.
  intros.
  destruct x.
  simpl.
  rewrite_Functor_list.
  auto.
Qed.

Lemma functor_law_2:
  forall a b c (f : a -> b) (g : b -> c) (x : Succs a),
  fmap g (fmap f x) = fmap (g ∘ f) x.
Proof.
  intros.
  destruct x.
  simpl.
  rewrite_Functor_list.
  auto.
Qed.

Instance instance_FunctorLaws_Succs : FunctorLaws Succs :=
  { functor_identity := functor_law_1;
    functor_composition := functor_law_2}
.

Lemma applicative_law_1:
  forall a (x : Succs a),
  (pure id <*> x) = x.
Proof.
  intros.
  destruct x.
  simpl.
  rewrite_Functor_list.
  auto.
Qed.

Lemma applicative_law_2:
  forall a b c
    (x : Succs (b -> c))
    (y : Succs (a -> b))
    (z : Succs a),
  (pure (_∘_) <*> x <*> y <*> z) = (x <*> (y <*> z)).
Proof.
  intros.
  destruct x, z, y.
  simpl.
  unfold op_z2218U__.
  f_equal.
  repeat (rewrite map_append || rewrite_Functor_list || rewrite append_assoc
      || unfold op_z2218U__ || unfold op_zd__).
  auto.
Qed.


Lemma applicative_law_3:
  forall a b (f : a -> b) (x : a),
  (pure f <*> pure x) = @pure Succs _ _ _ (f x).
Proof.
  intros.
  auto.
Qed.


Lemma applicative_law_4:
  forall a b (f : Succs (a -> b)) (x : a),
  (f <*> pure x) = (pure (fun y => y x) <*> f).
Proof.
  intros.
  destruct f.
  simpl.
  rewrite append_nil.
  auto.
Qed.

Instance instance_ApplicativeLaws_Succs : ApplicativeLaws Succs.
split.
exact applicative_law_1.
exact applicative_law_2.
exact applicative_law_3.
Qed.



Lemma monad_law_1:
  forall a b (x : a) (k : a -> Succs b),
  ((return_ x >>= k) = k x).
Proof.
  intros.
  simpl.
  destruct (k x).
  auto.
Qed.

Lemma monad_law_2:
  forall a (x : Succs a),
  (x >>= return_) = x.
Proof.
  intros.
  destruct x.
  simpl.
  rewrite append_nil.
  rewrite_Functor_list.
  auto.
Qed.

Lemma monad_law_3:
  forall a b c (m : Succs a) (k : a -> Succs b) (h : b -> Succs c),
  (m >>= (fun x => k x >>= h)) = ((m >>= k) >>= h).
Proof.
  intros.
  destruct m.
  simpl.
  unfold getCurrent, op_z2218U__, Successors.instance_GHC_BaseGen_Monad_Succs_op_zgzgze__, compose.
  destruct (k a0).
  destruct (h b0).
  f_equal.
  repeat (rewrite_Functor_list || rewrite map_append || rewrite append_assoc ||
    unfold getCurrent, op_z2218U__, Successors.instance_GHC_BaseGen_Monad_Succs_op_zgzgze__
    ).
  f_equal.
  apply map_cong; intro.
  destruct (k x).
  destruct (h b1).
  auto.
Qed.

Instance instance_MonadLaws_Succs : MonadLaws Succs.
split.
exact monad_law_1.
exact monad_law_2.
exact monad_law_3.
auto.
Qed.
