Require Import Prelude.
Require Import Successors.

Section list_proofs.

Lemma map_id:
  forall a (x : list a),
  map id x = x.
Proof.
  intros. induction x.
  * auto.
  * simpl. rewrite IHx. auto.
Qed.

Lemma map_map:
  forall a b c (f : a -> b) (g : b -> c) (x : list a),
  map g (map f x) = map (g ∘ f) x.
Proof.
  intros.
  induction x.
  * auto.
  * simpl. rewrite IHx. auto.
Qed.

Lemma map_append:
  forall a b (f : a -> b) (x y : list a),
  map f (x ++ y) = map f x ++ map f y.
Proof.
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

Lemma functor_law_1:
  forall a (x : Succs a),
  fmap id x = x.
Proof.
  intros.
  destruct x.
  simpl.
  rewrite map_id.
  auto.
Qed.

Lemma functor_law_2:
  forall a b c (f : a -> b) (g : b -> c) (x : Succs a),
  fmap g (fmap f x) = fmap (g ∘ f) x.
Proof.
  intros.
  destruct x.
  simpl.
  rewrite map_map.
  auto.
Qed.

Lemma applicative_law_1:
  forall a (x : Succs a),
  (pure id <*> x) = x.
Proof.
  intros.
  destruct x.
  simpl.
  rewrite map_id.
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
  repeat (rewrite map_append || rewrite map_map || rewrite append_assoc
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
  rewrite map_id.
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
  repeat (rewrite map_map || rewrite map_append || rewrite append_assoc ||
    unfold getCurrent, op_z2218U__, Successors.instance_GHC_BaseGen_Monad_Succs_op_zgzgze__ 
    ).
  f_equal.
  apply map_cong; intro.
  destruct (k x).
  destruct (h b1).
  auto.
Qed.

