(* This file contains the theory & tactics for definitions in the Base library.

   The Base library defines instances of the Functor/Applicative/Monad class
   for the option and list types.

   This library shows that those instances are lawful.

 *)

Require Import mathcomp.ssreflect.ssreflect.

Require Import GHC.Base.
Require Import GHC.BaseInstances.

Require Import Coq.Logic.FunctionalExtensionality.

(* Properties of basic functions *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.

Theorem hs_coq_map {A B} : map = @Coq.Lists.List.map A B.
Proof. extensionality f. extensionality l.
induction l; simpl; [|f_equal]; auto. Qed.

Theorem hs_coq_foldr_base {A B} : foldr = @Coq.Lists.List.fold_right A B.
Proof. extensionality f. extensionality z. extensionality l.
       induction l; simpl; [|f_equal]; auto. Qed.

Lemma map_id:
  forall a (x : list a),
  map id x = x.
Proof.
  intros. rewrite hs_coq_map. apply Coq.Lists.List.map_id.
Qed.

Lemma map_map:
  forall a b c (f : a -> b) (g : b -> c) (x : list a),
  map g (map f x) = map (g ∘ f) x.
Proof.
  intros.
  repeat rewrite hs_coq_map.
  apply Coq.Lists.List.map_map.
Qed.


Lemma map_append:
  forall a b (f : a -> b) (x y : list a),
  map f (x ++ y) = map f x ++ map f y.
Proof.
  intros.
  repeat rewrite hs_coq_map.
  apply Coq.Lists.List.map_app.
Qed.

Lemma map_cong:
  forall a b (f g : a -> b) (x : list a),
  (forall x, f x = g x) -> map f x = map g x.
Proof.
  intros.
  repeat rewrite hs_coq_map.
  apply Coq.Lists.List.map_ext.
  auto.
Qed.

Lemma flat_map_concat_map : forall A B (f : A -> list B) l,
    flat_map f l = concat (map f l).
Proof.
  intros.
  rewrite hs_coq_map.
  apply Coq.Lists.List.flat_map_concat_map.
Qed.

Lemma concat_map : forall A B (f : A -> B) l,
    map f (concat l) = concat (map (map f) l).
  intros.
  repeat rewrite hs_coq_map.
  apply Coq.Lists.List.concat_map.
Qed.

Lemma foldr_initial : forall A (x : list A), foldr (_::_) nil x = x.
Proof. induction x. simpl. auto. simpl. rewrite IHx. auto.
Qed.



Lemma flat_map_app : forall A B (f : A -> list B) xs ys,
  flat_map f (xs ++ ys) = flat_map f xs ++ flat_map f ys.
Proof.
  induction xs.
  - intros. rewrite app_nil_l.
    simpl. auto.
  - intros. simpl.
    rewrite <- app_assoc.
    rewrite IHxs.
    auto.
Qed.

Lemma flat_map_nil :
  forall A B (xs : list A),
    flat_map (fun x => nil) xs = (nil : list B).
Proof.
  induction xs. simpl. auto. simpl. auto.
Qed.


Lemma flat_map_cons_f : forall A B (f : A -> B) xs,
    flat_map (fun x => f x :: nil) xs = map f xs.
Proof.
  induction xs.
  - simpl. auto.
  - simpl. f_equal. auto.
Qed.

Lemma flat_map_cons_id:
  forall A (xs : list A),
  flat_map (fun x => x :: nil) xs = xs.
Proof.
  induction xs; auto. simpl. rewrite IHxs. reflexivity.
Qed.

Lemma flat_map_map : forall a b c (f : b -> list c) (g : a -> b) (u : list a),
  flat_map f (map g u) = flat_map (f ∘ g) u.
Proof.
  intros.
  rewrite flat_map_concat_map.
  rewrite map_map.
  rewrite <- flat_map_concat_map.
  auto.
Qed.

Lemma fmfm : forall a c (w : list a) (xs : list (a -> c)),
   flat_map (fun f : a -> c => flat_map (fun x : a => f x :: nil) w) xs =
   flat_map (fun f => map f w) xs.
Proof.
  induction xs. simpl. auto. simpl.
  rewrite IHxs.
  rewrite flat_map_cons_f. auto.
Qed.


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

Class MonadLaws (t : Type -> Type) `{ Monad t } `{ ApplicativeLaws t } :=
  { monad_left_id : forall A B (a :A) (k : A -> t B), (return_ a >>= k)  =  (k a);
    monad_right_id : forall A (m : t A),  (m >>= return_)  =  m;
    monad_composition : forall A B C (m : t A) (k : A -> t B) (h : B -> t C),
        (m >>= (fun x => k x >>= h))  =  ((m >>= k) >>= h);
    monad_applicative_pure : forall A (x:A), pure x = return_ x;
    monad_applicative_ap : forall A B (f : t (A -> B)) (x: t A), (f <*> x) = ap f x
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
         Base.instance_Monoid_unit_mappend,
         Base.instance_Monoid_unit_mempty,
         Base.instance_Monoid_unit_mconcat.
  - intro x. destruct x. auto.
  - intro x. destruct x. auto.
  - intros. auto.
  - intros x. induction x; simpl. auto. auto.
Qed.

Instance instance_MonoidLaws_comparison : MonoidLaws comparison.
Proof.
  split;
    repeat unfold mappend, mempty, mconcat, instance_Monoid_comparison,
    Base.instance_Monoid_comparison_mappend,
    Base.instance_Monoid_comparison_mempty,
    Base.instance_Monoid_comparison_mconcat.
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
    Base.instance_forall___Monoid_a___Monoid__option_a__mappend,
    Base.instance_forall___Monoid_a___Monoid__option_a__mconcat,
    Base.instance_forall___Monoid_a___Monoid__option_a__mempty.
  - destruct x; auto.
  - destruct x; auto.
  - intros x y z. destruct x; destruct y; destruct z; auto.
  - f_equal.
    destruct H. destruct H0.
    unfold Base.mappend, Base.mempty in *.
    rewrite monoid_assoc0. auto.
  - induction x; simpl. auto.
    destruct a0. auto.
    auto.
Qed.

Instance instance_MonoidLaws_list {a} : MonoidLaws (list a).
Proof.
  split;
    repeat unfold mappend, mempty, mconcat,
    instance_Monoid_list_a.
  - apply app_nil_l.
  - apply app_nil_r.
  - apply app_assoc.
  - induction x.
    simpl. auto.
    simpl. simpl in IHx.
    rewrite IHx.
    rewrite flat_map_cons_id.
    reflexivity.
Qed.



(* ------------------------- Functor --------------------------- *)

Instance instance_FunctorLaws_option : FunctorLaws option.
Proof.
  split;
    repeat unfold fmap, instance_Functor_option,
    Base.instance_Functor_option_fmap.
  - intros. destruct x; auto.
  - intros. destruct x; auto.
Qed.

Instance instance_FunctorLaws_list : FunctorLaws list.
Proof.
  split;
    repeat unfold fmap, instance_Functor_list,
    Base.instance_Functor_list_fmap.
  - exact map_id.
  - exact map_map.
Qed.


(* ------------------------- Applicative --------------------------- *)

Instance instance_ApplicativeLaws_option : ApplicativeLaws option.
Proof.
  split;
    repeat (unfold pure, instance_Applicative_option,
    Base.instance_Applicative_option_pure,
    Base.instance_Applicative_option_op_zlztzg__,
    Base.instance_Functor_option_fmap; simpl).
  - intros. destruct v; auto.
  - intros. destruct u; destruct v; destruct w; auto.
  - intros. auto.
  - intros. destruct u; auto.
Qed.

Instance instance_ApplicativeLaws_list : ApplicativeLaws list.
Proof.
  split;
    repeat (unfold pure, instance_Applicative_list,
    Base.instance_Applicative_list_pure,
    Base.instance_Applicative_list_op_zlztzg__,
    Base.instance_Functor_list_fmap; simpl).
  - intros. induction v; simpl; auto.
    simpl in IHv. rewrite IHv. auto.
  - intros.
    rewrite app_nil_r.
    repeat rewrite fmfm.
    rewrite flat_map_cons_f.
    rewrite flat_map_map.
    induction u.
    simpl. auto.
    simpl. rewrite <- IHu. clear IHu.
    rewrite flat_map_app.
    f_equal.
    induction v. simpl. auto.
    simpl. rewrite IHv.
    rewrite <- map_map.
    rewrite map_append.
    auto.
  - intros. auto.
  - intros. rewrite app_nil_r. auto.
Qed.

(* ------------------------- Monad  --------------------------- *)

Instance instance_MonadLaws_option : MonadLaws option.
Proof.
  split; intros;
   repeat (unfold pure, instance_Monad_option,
           Base.instance_Monad_option_op_zgzgze__,
           Base.instance_Monad_option_return_,
           instance_Applicative_option,
           Base.instance_Applicative_option_pure,
           Base.instance_Applicative_option_op_zlztzg__,
           Base.instance_Functor_option_fmap; simpl).
  - auto.
  - destruct m; auto.
  - destruct m; try destruct (k x); auto.
  - auto.
  - auto.
Qed.

Instance instance_MonadLaws_list : MonadLaws list.
Proof.
  split; intros;
    repeat (unfold pure,
            instance_Monad_list,
            Base.instance_Monad_list_op_zgzgze__,
            Base.instance_Monad_list_return_,
            instance_Applicative_list,
            Base.instance_Applicative_list_pure,
            Base.instance_Applicative_list_op_zlztzg__,
            Base.instance_Functor_list_fmap; simpl).
  - rewrite app_nil_r. rewrite flat_map_cons_id. auto.
  - rewrite flat_map_cons_id. auto.
  - induction m. simpl. auto.
    simpl. rewrite IHm.
    rewrite flat_map_app.
    f_equal.
    rewrite flat_map_cons_id.
    rewrite flat_map_cons_id.
    auto.
  - auto.
  - f_equal.
    extensionality g.
    rewrite flat_map_cons_id.
    auto.
Qed.

(* -------------------------------------------------------------------- *)
