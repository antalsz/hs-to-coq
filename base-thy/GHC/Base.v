(* This file contains the theory & tactics for definitions in the Base library.

   The Base library defines instances of the Functor/Applicative/Monad class
   for the option and list types.

   This library shows that those instances are lawful.

 *)

Require Import GHC.Base.

Require Import Coq.Logic.FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

(* Properties of basic functions *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.

Theorem hs_coq_map : @map = @Coq.Lists.List.map.
Proof.
  extensionality A; extensionality B; extensionality f; extensionality l.
  induction l; simpl; [|f_equal]; auto.
Qed.

Theorem hs_coq_foldr_base {A B} : @foldr A B = @Coq.Lists.List.fold_right B A.
Proof.
  extensionality f; extensionality z; extensionality l.
  induction l; simpl; [|f_equal]; auto.
Qed.

Theorem hs_coq_foldl_base {A B} (f : B -> A -> B) (z : B) (l : list A) :
  foldl f z l = Coq.Lists.List.fold_left f l z.
Proof. by rewrite /foldl; move: z; elim: l => //=. Qed.

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
  - simpl. auto.
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

Class EqLaws (t : Type) `{Eq_ t} :=
  { Eq_refl  : reflexive  _==_;
    Eq_sym   : symmetric  _==_;
    Eq_trans : transitive _==_;
    Eq_inv   : forall x y, x == y = ~~ (x /= y)
  }.

Theorem Neq_inv {t} `{EqLaws t} x y : x /= y = ~~ (x == y).
Proof. by rewrite Eq_inv negbK. Qed.

Theorem Neq_irrefl {t} `{EqLaws t} : irreflexive _/=_.
Proof. by move=> ?; rewrite Neq_inv Eq_refl. Qed.

Theorem Neq_sym {t} `{EqLaws t} : symmetric _/=_.
Proof. by move=> ? ?; rewrite !Neq_inv Eq_sym. Qed.

Theorem Neq_atrans {t} `{EqLaws t} y x z : x /= z -> (x /= y) || (y /= z).
Proof. rewrite !Neq_inv -negb_andb; apply contra => /andP[]; apply Eq_trans. Qed.

Class EqExact (t : Type) `{EqLaws t} :=
  { Eq_eq : forall x y, reflect (x = y) (x == y) }.

Lemma Build_EqLaws_reflect (t : Type) `{Eq_ t} :
  (forall x y : t, reflect (x = y) (x == y)) ->
  (forall x y, x == y = ~~ (x /= y))         ->
  EqLaws t.
Proof.
  move=> Eq_eq Eq_inv; constructor.
  - by move=> x; apply/Eq_eq.
  - move=> x y; case: (Eq_eq x y); case: (Eq_eq y x); congruence.
  - by move=> x y z /Eq_eq -> /Eq_eq ->; apply/Eq_eq.
  - apply Eq_inv.
Qed.

Ltac EqLaws_from_reflect Eq_eq_t :=
  apply Build_EqLaws_reflect; [by apply Eq_eq_t | try by move=> * /=; rewrite negbK].

Theorem Eq_eq_Int (x y : Int) : reflect (x = y) (x == y).
Proof.
  unfold op_zeze__, Eq_Integer___, op_zeze____.
  case H: (_ =? _)%Z; constructor.
  - by apply Z.eqb_eq.
  - by rewrite -Z.eqb_eq H.
Qed.

Instance EqLaws_Int : EqLaws Int.
Proof. EqLaws_from_reflect Eq_eq_Int. Qed.

Instance EqExact_Int : EqExact Int.
Proof. constructor; apply Eq_eq_Int. Qed.


Instance EqLaws_Integer  : EqLaws  Integer := EqLaws_Int.
Instance EqExact_Integer : EqExact Integer := EqExact_Int.


Theorem Eq_eq_Word (x y : Word) : reflect (x = y) (x == y).
Proof.
 unfold op_zeze__, Eq_Word___, op_zeze____, Eq_Char___.
 case H: (_ =? _)%N; constructor.
 - by apply N.eqb_eq.
 - by rewrite -N.eqb_eq H.
Qed.

Instance EqLaws_Word : EqLaws Word.
Proof. EqLaws_from_reflect Eq_eq_Word. Qed.

Instance EqExact_Word : EqExact Word.
Proof. constructor; apply Eq_eq_Word. Qed.


Instance EqLaws_Char  : EqLaws  Char := EqLaws_Word.
Instance EqExact_Char : EqExact Char := EqExact_Word.

Theorem Eq_eq_bool (x y : bool) : reflect (x = y) (x == y).
Proof. by case: x; case: y; constructor. Qed.

Instance EqLaws_bool : EqLaws bool.
Proof. EqLaws_from_reflect Eq_eq_bool. Qed.

Instance EqExact_bool : EqExact bool.
Proof. constructor; apply Eq_eq_bool. Qed.


Instance EqLaws_unit : EqLaws unit.
Proof. by split. Qed.

Instance EqExact_unit : EqExact unit.
Proof. by split; repeat case; constructor. Qed.


Instance EqLaws_comparison : EqLaws comparison.
Proof. by split; repeat case. Qed.

Instance EqExact_comparison : EqExact comparison.
Proof. by split; repeat case; constructor. Qed.


Instance EqLaws_list {a} `{EqLaws a} : EqLaws (list a).
Proof.
  split;
  unfold op_zeze__, op_zsze__, Eq_list, op_zeze____, op_zsze____.
  - by elim=> [|x xs IH] //=; rewrite Eq_refl.
  - elim=> [|x xs /= IH] //=; first by case.
    by case=> [|y ys] //=; rewrite Eq_sym IH.
  - elim=> [|y ys /= IH] //=; first by case.
    case=> [|x xs] //= [|z zs] //=.
    move=> /andP [eq_x_y eq_xs_ys] /andP [eq_y_z eq_ys_zs].
    apply/andP; split; first by apply (Eq_trans y).
    by apply IH.
  - by move=> * /=; rewrite negbK.
Qed.

Instance EqExact_list {a} `{EqExact a} : EqExact (list a).
Proof.
  split; unfold op_zeze__, op_zsze__, Eq_list, op_zeze____, op_zsze____;
  elim=> [|x xs /= IH]; first by case; constructor.
  case=> [|y ys] //=; first by constructor.
  case: (IH ys) => [-> | NEQ].
  - case E: (x == y); constructor; move/Eq_eq in E.
    + by rewrite E.
    + by contradict E; case: E.
  - by rewrite andbF; constructor; contradict NEQ; case: NEQ.
Qed.


Instance EqLaws_option {a} `{EqLaws a} : EqLaws (option a).
Proof.
  split; rewrite /op_zeze__ /op_zsze__ /Eq___option /op_zeze____ /op_zsze____.
  - case=> [?|] //=; apply Eq_refl.
  - repeat case=> [?|] //=; apply Eq_sym.
  - repeat case=> [?|] //=; apply Eq_trans.
  - repeat case=> [?|] //=. rewrite negb_involutive. reflexivity.
Qed.

Instance EqExact_option {a} `{EqExact a} : EqExact (option a).
Proof.
  split; unfold op_zeze__, op_zsze__, Eq___option, op_zeze____, op_zsze____
    => - [x|] [y|] //=; try by constructor.
  case E: (x == y); constructor; move/Eq_eq in E.
  - by rewrite E.
  - by contradict E; case: E.
Qed.

(* -------------------------------------------------------------------- *)

Class MonoidLaws (t : Type) `{ Monoid t } :=
  { monoid_left_id  : forall x, mappend mempty x = x;
    monoid_right_id : forall x, mappend x mempty = x;
    monoid_assoc    : forall x y z, mappend x (mappend y z) = mappend (mappend x y) z;
    monoid_mconcat  : forall x, mconcat x = foldr mappend mempty x
  }.

Class FunctorLaws (t : Type -> Type) `{Functor t} :=
    {
      functor_identity    : forall a (x: t a), fmap id x = x;
      functor_composition : forall a b c (f : a -> b) (g : b -> c) (x : t a),
          fmap g (fmap f x) = fmap (g ∘ f) x
    }.

Class ApplicativeLaws (t : Type -> Type) `{!Functor t, !Applicative t, !FunctorLaws t} :=
 { applicative_identity : forall a (v : t a), (pure id <*> v) = v;
   applicative_composition : forall a b c (u : t (b -> c)) (v : t (a -> b)) (w : t a),
     (pure _∘_ <*> u <*> v <*> w) = (u <*> (v <*> w));
   applicative_homomorphism : forall a b (f : a -> b) (x : a),
     (pure f <*> pure x) = (pure (f x));
   applicative_interchange : forall a b (u : t (a -> b)) (y : a),
     (u <*> pure y) = ((pure (fun x => x y)) <*> u);
   applicative_fmap : forall a b (f : a -> b) (x : t a),
     fmap f x = (pure f <*> x)
     (* free theorem *)
 }.

Class MonadLaws (t : Type -> Type) `{!Functor t, !Applicative t, !Monad t, !FunctorLaws t, !ApplicativeLaws t} :=
  { monad_left_id : forall A B (a :A) (k : A -> t B), (return_ a >>= k)  =  (k a);
    monad_right_id : forall A (m : t A),  (m >>= return_)  =  m;
    monad_composition : forall A B C (m : t A) (k : A -> t B) (h : B -> t C),
        (m >>= (fun x => k x >>= h))  =  ((m >>= k) >>= h);
    monad_applicative_pure : forall A (x:A), pure x = return_ x;
    monad_applicative_ap : forall A B (f : t (A -> B)) (x: t A), (f <*> x) = ap f x
  }.

Class MonadPlusLaws (t : Type -> Type) `{!Functor t, !Applicative t, !Monad t, !Alternative t, !MonadPlus t, !FunctorLaws t, !ApplicativeLaws t, !MonadLaws t} :=
  { mzero_left : forall A B (f : A -> t B), (mzero >>= f)  =  mzero;
    mzero_right: forall A B (v : t A), (v >> mzero)   =  (mzero : t B);
    mplus_associative : forall A (f g h : t A),
          mplus f (mplus g h) = mplus (mplus f g) h;
  }.

(* ------------------------- Monoid --------------------------- *)

Instance instance_MonoidLaws_unit : MonoidLaws unit.
Proof.
  split;
    unfold mappend, mempty, mconcat, Monoid__unit,
         Base.Monoid__unit_mappend,
         Base.Monoid__unit_mempty,
         Base.Monoid__unit_mconcat.
  - intro x. destruct x. auto.
  - intro x. destruct x. auto.
  - intros. auto.
  - intros x. induction x; simpl. auto. auto.
Qed.

Instance instance_MonoidLaws_comparison : MonoidLaws comparison.
Proof.
  split;
    repeat unfold mappend, mempty, mconcat, instance_Monoid_comparison,
    Base.Monoid__comparison_mappend,
    Base.Monoid__comparison_mempty,
    Base.Monoid__comparison_mconcat.
  - intro x. auto.
  - intro x. destruct x; auto.
  - intros. destruct x; destruct y; auto.
  - intros x. induction x; simpl; auto.
Qed.

Instance instance_MonoidLaws_option {a} `{ MonoidLaws a } : MonoidLaws (option a).
Proof.
  split;
    repeat unfold mappend, mempty, mconcat,
    Base.Monoid__option,
    Base.Monoid__option_mappend,
    Base.Monoid__option_mconcat,
    Base.Monoid__option_mempty.
  - destruct x; auto.
  - destruct x; auto.
  - intros x y z.
    simpl; repeat fold mappend.
    destruct x; destruct y; destruct z; auto.
    f_equal.
    apply monoid_assoc.
  - induction x; simpl. auto.
    destruct a0. auto.
    auto.
Qed.

Instance instance_MonoidLaws_list {a} : MonoidLaws (list a).
Proof.
  split.
  - apply app_nil_l.
  - apply app_nil_r.
  - apply app_assoc.
  - induction x.
    * simpl. auto.
    * simpl.
      unfold mconcat, Monoid__list in *; simpl in *.
      rewrite IHx.
      rewrite flat_map_cons_id.
      reflexivity.
Qed.


(* ------------------------- Functor --------------------------- *)

Instance instance_FunctorLaws_option : FunctorLaws option.
Proof.
  split;
    repeat unfold fmap, Functor__option,
    Base.Functor__option_fmap.
  - intros. destruct x; auto.
  - intros. destruct x; auto.
Qed.

Instance instance_FunctorLaws_list : FunctorLaws list.
Proof.
  split;
    repeat unfold fmap, Functor__list,
    Base.Functor__list_fmap.
  - exact map_id.
  - exact map_map.
Qed.


(* ------------------------- Applicative --------------------------- *)

Instance instance_ApplicativeLaws_option : ApplicativeLaws option.
Proof.
  split;
    repeat (unfold pure, Applicative__option,
    Base.Applicative__option_pure,
    Base.Applicative__option_op_zlztzg__,
    Base.Functor__option_fmap; simpl).
  - intros. destruct v; auto.
  - intros. destruct u; destruct v; destruct w; auto.
  - intros. auto.
  - intros. destruct u; auto.
  - reflexivity.
Qed.

Instance instance_ApplicativeLaws_list : ApplicativeLaws list.
Proof.
  split;
    repeat (unfold
      op_zlztzg__,
      pure, Applicative__list,
      Base.Applicative__list_pure,
      Base.Applicative__list_op_zlztzg__,
      Base.Functor__list_fmap; simpl).
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
  - by move=> *; rewrite flat_map_cons_f app_nil_r.
Qed.

(* ------------------------- Monad  --------------------------- *)

Instance instance_MonadLaws_option : MonadLaws option.
Proof.
  split; intros;
   repeat (unfold pure, instance_Monad__option,
           Base.Monad__option_op_zgzgze__,
           Base.Monad__option_return_,
           Base.Applicative__option,
           Base.Applicative__option_pure,
           Base.Applicative__option_op_zlztzg__,
           Base.Functor__option_fmap; simpl).
  - auto.
  - destruct m; auto.
  - destruct m; try destruct (k x); auto.
  - auto.
  - auto.
Qed.

Instance instance_MonadLaws_list : MonadLaws list.
Proof.
  split; intros;
    repeat (unfold pure, GHC.Base.op_zgzgze__, GHC.Base.op_zlztzg__, ap,
            Base.Monad__list,
            Base.Monad__list_op_zgzgze__,
            Base.Monad__list_return_,
            Base.Applicative__list,
            Base.Applicative__list_pure,
            Base.Applicative__list_op_zlztzg__,
            Base.Functor__list_fmap; simpl).
  - simpl.
    rewrite app_nil_r. rewrite flat_map_cons_id. auto.
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
