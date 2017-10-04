(* This file contains the theory & tactics for definitions in the BaseGen library. *)

Require Import GHC.BaseGen.

(* Properties of basic functions *)

Lemma map_id:
  forall a (x : list a),
  map id x = x.
Proof.
  intros.
  intros.
  induction x.
  * auto.
  * simpl. rewrite IHx. auto.
Qed.

Lemma map_map:
  forall a b c (f : a -> b) (g : b -> c) (x : list a),
  map g (map f x) = map (g ∘ f) x.
Proof.
  intros.
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

(* -------------------------------------------------------------------- *)

(* Monoid instances that don't yet translate *)

Instance instance_Monoid_list_a {a} : Monoid (list a) :=
  { mempty  := nil;
    mappend := (_++_);
    mconcat := fun xss => concatMap (fun xs => concatMap (fun x => x :: nil) xs) xss
  }.

Instance instance_Monoid_arrow {a}{b} `{Monoid b} : Monoid (a -> b) :=
  {
    mempty  := fun _ => (mempty : b);
    mappend := fun f g x => mappend (f x) (g x);
    mconcat := foldr (fun f g x => mappend (f x) (g x)) (fun _ => mempty)
  }.

(* -------------------------------------------------------------------- *)

Class MonoidLaws (t : Type) `{ Monoid t } :=
  { monoid_left_id  : forall x, mappend mempty x = x;
    monoid_right_id : forall x, mappend x mempty = x;
    monoid_assoc    : forall x y z, mappend x (mappend y z) = mappend (mappend x y) z;
    monoid_mconcat  : forall x, mconcat x = foldr mappend mempty x
  }.

Class FunctorLaws (t : Type -> Type) `{ Functor t } :=
    {
      functor_identity    : forall a (x: t a), fmap id x = x;
      functor_composition : forall a b c (f : a -> b) (g : b -> c) (x : t a),
          fmap g (fmap f x) = fmap (g ∘ f) x
    }.

Class ApplicativeLaws (t : Type -> Type) `{ Applicative t } `{ FunctorLaws t} :=
 { applicative_identity : forall a (v : t a), (pure id <*> v) = v;
   applicative_composition : forall a b c (u : t (b -> c)) (v : t (a -> b)) (w : t a),
     (pure _∘_ <*> u <*> v <*> w) = (u <*> (v <*> w));
   applicative_homomorphism : forall a b (f : a -> b) (x : a),
     (pure f <*> pure x) = (pure (f x));
   applicative_interchange : forall a b (u : t (a -> b)) (y : a),
     (u <*> pure y) = ((pure (fun x => x y)) <*> u)
 }.

(*
Class AlternativeLaws (t : Type -> Type) `{ Alternative t } `{ ApplicativeLaws t } :=
  { alternative_left_identity :
*)

Class MonadLaws (t : Type -> Type) `{ Monad t } `{ ApplicativeLaws t } :=
  { monad_left_id : forall A B (a :A) (k : A -> t B), (return_ a >>= k)  =  (k a);
    monad_right_id : forall A (m : t A),  (m >>= return_)  =  m;
    monad_composition : forall A B C (m : t A) (k : A -> t B) (h : B -> t C),
        (m >>= (fun x => k x >>= h))  =  ((m >>= k) >>= h);
    monad_applicative_pure : forall A (x:A), pure x = return_ x;
(*    monad_applicative_ap : forall A B (f : A -> B) (x: t A), (f <*> x) = ap f x *)
  }.

Class MonadPlusLaws (t : Type -> Type) `{ MonadPlus t} `{ MonadLaws t } :=
  { mzero_left : forall A B (f : A -> t B), (mzero >>= f)  =  mzero;
    mzero_right: forall A B (v : t A), (v >> mzero)   =  (mzero : t B);
    mplus_associative : forall A (f g h : t A),
          mplus f (mplus g h) = mplus (mplus f g) h;
  }.


(* ------------------------- Monoid --------------------------- *)

Instance instance_MonoidLaws_unit : MonoidLaws unit.
Proof.
  split;
    unfold mappend, mempty, mconcat, instance_Monoid_unit,
         BaseGen.instance_Monoid_unit_mappend,
         BaseGen.instance_Monoid_unit_mempty,
         BaseGen.instance_Monoid_unit_mconcat.
  - intro x. destruct x. auto.
  - intro x. destruct x. auto.
  - intros. auto.
  - intros x. induction x; simpl. auto. auto.
Qed.

Instance instance_MonoidLaws_comparison : MonoidLaws comparison.
Proof.
  split;
    repeat unfold mappend, mempty, mconcat, instance_Monoid_comparison,
    BaseGen.instance_Monoid_comparison_mappend,
    BaseGen.instance_Monoid_comparison_mempty,
    BaseGen.instance_Monoid_comparison_mconcat.
  - intro x. auto.
  - intro x. destruct x; auto.
  - intros. destruct x; destruct y; auto.
  - intros x. induction x; simpl; auto.
Qed.

Instance instance_MonoidLaws_option {a} `{ MonoidLaws a } : MonoidLaws (option a).
Proof.
  split;
    repeat unfold mappend, mempty, mconcat,
    instance_forall___Monoid_a___Monoid__option_a_,
    BaseGen.instance_forall___Monoid_a___Monoid__option_a__mappend,
    BaseGen.instance_forall___Monoid_a___Monoid__option_a__mconcat,
    BaseGen.instance_forall___Monoid_a___Monoid__option_a__mempty.
  - destruct x; auto.
  - destruct x; auto.
  - intros x y z. destruct x; destruct y; destruct z; auto.
  - f_equal.
    destruct H. destruct H0.
    unfold BaseGen.mappend, BaseGen.mempty in *.
    rewrite monoid_assoc0. auto.
  - induction x; simpl. auto.
    destruct a0. auto.
    auto.
Qed.

Lemma foldr_initial : forall A (x : list A), Prim.foldr (_::_) nil x = x.
Proof. induction x. simpl. auto. simpl. rewrite IHx. auto.
Qed.

Instance instance_MonoidLaws_list {a} : MonoidLaws (list a).
Proof.
  split;
    repeat unfold mappend, mempty, mconcat,
    instance_Monoid_list_a.
  - apply app_nil_l.
  - apply app_nil_r.
  - apply app_assoc.
  - unfold concatMap; simpl.
    unfold compose.
    induction x.
    simpl. auto.
    simpl. simpl in IHx.
    rewrite IHx.
    rewrite foldr_initial.
    auto.
Qed.

(* ------------------------- Functor --------------------------- *)

Instance instance_FunctorLaws_option : FunctorLaws option.
Proof.
  split;
    repeat unfold fmap, instance_Functor_option,
    BaseGen.instance_Functor_option_fmap.
  - intros. destruct x; auto.
  - intros. destruct x; auto.
Qed.

Instance instance_FunctorLaws_list : FunctorLaws list.
Proof.
  split;
    repeat unfold fmap, instance_Functor_list,
    BaseGen.instance_Functor_list_fmap.
  - exact map_id.
  - exact map_map.
Qed.

(* ------------------------- Applicative --------------------------- *)

Instance instance_ApplicativeLaws_option : ApplicativeLaws option.
Proof.
  split;
    repeat (unfold pure, instance_Applicative_option,
    BaseGen.instance_Applicative_option_pure,
    BaseGen.instance_Applicative_option_op_zlztzg__,
    BaseGen.instance_Functor_option_fmap; simpl).
  - intros. destruct v; auto.
  - intros. destruct u; destruct v; destruct w; auto.
  - intros. auto.
  - intros. destruct u; auto.
Qed.

Instance instance_ApplicativeLaws_list : ApplicativeLaws list.
Proof.
  split;
    repeat (unfold pure, instance_Applicative_list,
    BaseGen.instance_Applicative_list_pure,
    BaseGen.instance_Applicative_list_op_zlztzg__,
    BaseGen.instance_Functor_list_fmap; simpl).
  - intros. induction v; repeat (unfold concatMap, compose in *; simpl); auto.
    simpl in IHv. rewrite IHv. auto.
  - intros.
    unfold concatMap.
Abort.

(* ------------------------- Monad  --------------------------- *)