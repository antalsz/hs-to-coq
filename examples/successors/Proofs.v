Require Import Prelude.
Require Import Control.Applicative.Successors.
Require Import Proofs.GHC.Base.

Ltac unfold_Control_Applicative_Successors_Succs_Instances :=
  repeat
  unfold Successors.instance_GHC_Base_Functor_Control_Applicative_Successors_Succs,
         Successors.instance_GHC_Base_Applicative_Control_Applicative_Successors_Succs,
         Successors.instance_GHC_Base_Monad_Control_Applicative_Successors_Succs,
         Successors.instance_GHC_Base_Functor_Control_Applicative_Successors_Succs_fmap,
         Successors.instance_GHC_Base_Applicative_Control_Applicative_Successors_Succs_pure,
         Successors.instance_GHC_Base_Applicative_Control_Applicative_Successors_Succs_op_zlztzg__,
         Successors.instance_GHC_Base_Monad_Control_Applicative_Successors_Succs_op_zgzgze__,
         Successors.instance_GHC_Base_Monad_Control_Applicative_Successors_Succs_return_.


(* A tactic to rewrite with the list functor *)
Ltac rewrite_Functor_list :=
  let K := fresh in
  let L := fresh in
  pose (K := @functor_identity list instance_GHC_Base_Functor_list instance_FunctorLaws_list); clearbody K;
  pose (L := @functor_composition list instance_GHC_Base_Functor_list instance_FunctorLaws_list); clearbody L;
  try rewrite K; try rewrite L;
  unfold fmap, instance_GHC_Base_Functor_list, Base.instance_GHC_Base_Functor_list_fmap in K, L;
  try rewrite K; try rewrite L;
  clear K; clear L.




Lemma functor_law_1:
  forall a (x : Succs a),
  fmap id x = x.
Proof.
  intros.
  destruct x.
  unfold fmap, fmap__, instance_GHC_Base_Functor_Control_Applicative_Successors_Succs. simpl.
  rewrite_Functor_list.
  auto.
Qed.

Lemma functor_law_2:
  forall a b c (f : a -> b) (g : b -> c) (x : Succs a),
  fmap g (fmap f x) = fmap (g ∘ f) x.
Proof.
  intros.
  destruct x.
  unfold fmap, fmap__, instance_GHC_Base_Functor_Control_Applicative_Successors_Succs. simpl.
  rewrite_Functor_list.
  auto.
Qed.

Instance instance_FunctorLaws_Control_Applicative_Successors_Succs : FunctorLaws Succs :=
  { functor_identity := functor_law_1;
    functor_composition := functor_law_2}
.

Lemma applicative_law_1:
  forall a (x : Succs a),
  (pure id <*> x) = x.
Proof.
  intros.
  destruct x.
  unfold op_zlztzg__, op_zlztzg____, pure, pure__,
         instance_GHC_Base_Applicative_Control_Applicative_Successors_Succs. simpl.
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
  unfold op_zlztzg__, op_zlztzg____, pure, pure__,
         instance_GHC_Base_Applicative_Control_Applicative_Successors_Succs. simpl.
  f_equal.
  repeat (rewrite map_append || rewrite_Functor_list || rewrite app_assoc).
  reflexivity.
Qed.


Lemma applicative_law_3:
  forall a b (f : a -> b) (x : a),
  (pure f <*> pure x) = @pure Succs _ _ _ (f x).
Proof.
  intros.
  reflexivity.
Qed.


Lemma applicative_law_4:
  forall a b (f : Succs (a -> b)) (x : a),
  (f <*> pure x) = (pure (fun y => y x) <*> f).
Proof.
  intros.
  destruct f.
  unfold op_zlztzg__, op_zlztzg____, pure, pure__,
         instance_GHC_Base_Applicative_Control_Applicative_Successors_Succs. simpl.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.


Lemma applicative_law_5:
  forall (a b : Type) (f : a -> b) (x : Succs a), fmap f x = _<*>_ (pure f) x.
Proof.
  intros.
  reflexivity.
Qed.

Instance instance_ApplicativeLaws_Control_Applicative_Successors_Succs : ApplicativeLaws Succs.
split.
exact applicative_law_1.
exact applicative_law_2.
exact applicative_law_3.
exact applicative_law_4.
exact applicative_law_5.
Qed.



Lemma monad_law_1:
  forall a b (x : a) (k : a -> Succs b),
  ((return_ x >>= k) = k x).
Proof.
  intros.
  unfold op_zgzgze__, op_zgzgze____, return_, return___,
         instance_GHC_Base_Monad_Control_Applicative_Successors_Succs. simpl.
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
  unfold op_zgzgze__, op_zgzgze____, return_, return___,
         instance_GHC_Base_Monad_Control_Applicative_Successors_Succs. simpl.
  simpl.
  rewrite map_id.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma monad_law_3:
  forall a b c (m : Succs a) (k : a -> Succs b) (h : b -> Succs c),
  (m >>= (fun x => k x >>= h)) = ((m >>= k) >>= h).
Proof.
  intros.
  destruct m.
  unfold op_zgzgze__, op_zgzgze____, return_, return___,
         instance_GHC_Base_Monad_Control_Applicative_Successors_Succs. simpl.
  unfold_Control_Applicative_Successors_Succs_Instances.
  unfold getCurrent, op_z2218U__, compose.
  destruct (k a0).
  destruct (h b0).
  f_equal.
  repeat (rewrite_Functor_list || rewrite map_append || rewrite <- app_assoc ||
    unfold getCurrent, op_z2218U__).
  f_equal.
  apply map_cong; intro.
  destruct (k x).
  destruct (h b1).
  reflexivity.
Qed.


Lemma monad_law_5 :
  forall (A B : Type) (f : Succs (A -> B)) (x : Succs A), _<*>_ f x = ap f x.
Proof.
  intros.
  destruct f. destruct x.
  unfold ap, op_zgzgze__, op_zgzgze____, return_, return___,
         op_zlztzg__, op_zlztzg____,
         instance_GHC_Base_Monad_Control_Applicative_Successors_Succs, instance_GHC_Base_Applicative_Control_Applicative_Successors_Succs. simpl.
  f_equal.
  unfold compose.
  rewrite app_nil_r.
  f_equal.
Qed.


Instance instance_MonadLaws_Control_Applicative_Successors_Succs : MonadLaws Succs.
split.
exact monad_law_1.
exact monad_law_2.
exact monad_law_3.
reflexivity.
exact monad_law_5.
Qed.
