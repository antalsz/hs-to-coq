(* This file contains the theory & tactics for definitions in the Base library.

   The Base library defines instances of the Functor/Applicative/Monad class
   for the option and list types.

   This library shows that those instances are lawful.

 *)

Require Import GHC.Base.
Require Import Data.Semigroup.

Set Warnings "-notation-overridden".
From Coq Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

(* Properties of basic functions *)

Require Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.


(* ** hs_simpl tactic *) 

(*
   Furthermore, this file defines a rewriting database hs_simpl and 
   associated tactic (hs_simpl) for simplifying Haskell expressions
   and unfolding type class applications.
*)

Ltac hs_simpl := autorewrite with hs_simpl.

Tactic Notation "hs_simpl" "in" hyp(h) := autorewrite with hs_simpl in h.


(** ** [Lists] *)
(* Haskell-Coq equivalence *)

Theorem hs_coq_map : @map = @Coq.Lists.List.map.
Proof. reflexivity. Qed.

Theorem hs_coq_foldr_base {A B} : @foldr A B = @Coq.Lists.List.fold_right B A.
Proof. reflexivity. Qed.

Theorem hs_coq_foldl_base {A B} (f : B -> A -> B) (z : B) (l : list A) :
  foldl f z l = Coq.Lists.List.fold_left f l z.
Proof. by rewrite /foldl; move: z; elim: l => //=. Qed.

(* ---------- foldr ------------------------------ *)

Lemma foldr_initial {A} (x : list A) : foldr (_::_) nil x = x.
Proof. by elim: x => //= x xs ->. Qed.
Hint Rewrite @foldr_initial : hs_simpl.

Lemma foldr_single {A B} (k : A -> B -> B) z x : foldr k z (x :: nil) = k x z.
Proof. done. Qed.

Lemma foldr_nil {A B} (k : A -> B -> B) z : foldr k z nil = z.
Proof. done. Qed.

Hint Rewrite @foldr_initial @foldr_single @foldr_nil : hs_simpl.

Lemma foldr_id {A B} (a : A) (bs : list B) : foldr (fun _ => id) a bs = a.
Proof. by elim: bs. Qed.

(* ---------- append ------------------------------ *)

(* Because we map Haskell's append to Coq's ++ directly. All of the 
   Coq theorems are automatically available. However, we make these
   automatically available to hs_simpl. *)

Hint Rewrite @app_nil_r @app_length : hs_simpl.

(* ---------- map ------------------------------ *)

Lemma map_id {a} (x : list a) : map id x = x.
Proof. by rewrite hs_coq_map Coq.Lists.List.map_id. Qed.
Hint Rewrite @map_id : hs_simpl.

Lemma map_map {a b c} (f : a -> b) (g : b -> c) (x : list a) :
  map g (map f x) = map (g ∘ f) x.
Proof. by rewrite !hs_coq_map Coq.Lists.List.map_map. Qed.

Lemma map_append {a b} (f : a -> b) (x y : list a) :
  map f (x ++ y) = map f x ++ map f y.
Proof. by rewrite !hs_coq_map Coq.Lists.List.map_app. Qed.

Hint Rewrite @map_append : hs_simpl.

Lemma map_cong {a b} (f g : a -> b) (x : list a) :
  f =1 g -> map f x = map g x.
Proof. by rewrite !hs_coq_map => /Coq.Lists.List.map_ext ->. Qed.

Lemma concat_map {A B} (f : A -> B) l : 
  map f (concat l) = concat (map (map f) l).
Proof. by rewrite !hs_coq_map Coq.Lists.List.concat_map. Qed.

(* ---------------- flat map ----------------------- *)

Lemma flat_map_concat_map {A B} (f : A -> list B) l :
 flat_map f l = concat (map f l).
Proof. by rewrite !hs_coq_map Coq.Lists.List.flat_map_concat_map. Qed.

Lemma flat_map_app {A B} (f : A -> list B) xs ys :
  flat_map f (xs ++ ys) = flat_map f xs ++ flat_map f ys.
Proof. by elim: xs => //= x xs ->; rewrite app_assoc. Qed.

Lemma flat_map_nil {A B} (xs : list A) :
  flat_map (fun _ => nil) xs = nil :> list B.
Proof. by elim: xs. Qed.

Lemma flat_map_cons_f {A B} (f : A -> B) xs :
  flat_map (fun x => f x :: nil) xs = map f xs.
Proof. by elim: xs. Qed.

Lemma flat_map_cons_id {A} (xs : list A) :
  flat_map (fun x => x :: nil) xs = xs.
Proof. by elim: xs => //= x xs ->. Qed.

Lemma flat_map_map {a b c} (f : b -> list c) (g : a -> b) (u : list a) :
  flat_map f (map g u) = flat_map (f ∘ g) u.
Proof. by rewrite !flat_map_concat_map map_map. Qed.

Lemma flat_map_cong {a b} (f g : a -> list b) xs :
  f =1 g -> flat_map f xs = flat_map g xs.
Proof. by rewrite !flat_map_concat_map => /map_cong ->. Qed.

Lemma fmfm {a c} (w : list a) (xs : list (a -> c)) :
   flat_map (fun f => flat_map (fun x : a => f x :: nil) w) xs =
   flat_map (fun f => map f w) xs.
Proof. by elim: xs. Qed. (* ??? That works?! *)

(* -------------------------------------------------------------------- *)

(** ** [Eq_] instances *)

Class EqLaws (t : Type) `{Eq_ t} :=
  { Eq_refl  : reflexive  _==_;
    Eq_sym   : symmetric  _==_;
    Eq_trans : transitive _==_;
    Eq_inv   : forall x y : t, x == y = ~~ (x /= y)
  }.

Theorem Neq_inv {t} `{EqLaws t} x y : x /= y = ~~ (x == y).
Proof. by rewrite Eq_inv negbK. Qed.

Theorem Neq_irrefl {t} `{EqLaws t} : irreflexive _/=_.
Proof. by move=> ?; rewrite Neq_inv Eq_refl. Qed.

Theorem Neq_sym {t} `{EqLaws t} : symmetric _/=_.
Proof. by move=> ? ?; rewrite !Neq_inv Eq_sym. Qed.

Theorem Neq_atrans {t} `{EqLaws t} y x z : x /= z -> (x /= y) || (y /= z).
Proof. rewrite !Neq_inv -negb_andb; apply contra => /andP[]; apply Eq_trans. Qed.

Lemma Eq_reflI {t} `{EqLaws t} : forall x y, x = y -> x == y = true.
Proof. intros. subst. apply Eq_refl. Qed.

Instance Eq_Reflexive : forall {a} `{EqLaws a}, Reflexive (fun (x y:a) => x == y).
Proof. intros. eapply Eq_refl. Qed.

Instance Eq_Symmetric : forall {a} `{EqLaws a}, Symmetric (fun (x y:a) => x == y).
Proof. move=> ?????. rewrite Eq_sym. done. Qed.

Instance Eq_Transitive : forall {a} `{EqLaws a}, Transitive (fun (x y:a) => x == y).
Proof. move=> ??????. apply Eq_trans. Qed.

Instance Eq_Equivalence :  forall {a} `{EqLaws a}, Equivalence (fun (x y:a) => x == y).
Proof. move=> ???. split; typeclasses eauto. Qed.  

Instance Eq_is_true_m : forall {a} `{EqLaws a},
    Proper ((fun (x y:a) => x == y) ==> (fun (x y:a) => x == y) ==> iff)
           (fun (x y:a) => x == y).
Proof.
  move=> a EQ EL x1 x2 ex y1 y2 ey.
  split.
  intro h.
  eapply Eq_trans.
  rewrite Eq_sym in ex.
  eauto.
  eapply Eq_trans. eapply h. eauto.
  intro h.
  eapply Eq_trans.
  eapply ex.
  eapply Eq_trans.
  eapply h.
  rewrite Eq_sym.
  eapply ey.
Qed.


Instance Eq_m : forall {a}`{EqLaws a},
  Proper ((_==_) ==> (_==_) ==> Logic.eq)
  (_==_).
Proof.
  move=> a HE HE2 x1 x2 Hx y1 y2 Hy.
  destruct (x1 == y1) eqn:E1; destruct (x2 == y2) eqn:E2; auto.
  assert (x2 == y2).
  { eapply Eq_trans.
    rewrite Eq_sym.
    eauto.
    eapply Eq_trans. eauto. eauto. }
  rewrite H in E2. inversion E2.
  assert (x1 == y1).
  { eapply Eq_trans.
    eauto.
    eapply Eq_trans. eauto.
    rewrite Eq_sym. eauto.
  } 
  rewrite H in E1. inversion E1.
Qed.

(* I would love to be able to use rewriting instead of this 
   lemma to do this. Why doesn't it work??? *)
Lemma eq_replace_r : forall {a} `{EqLaws a}  (v1 v2 v3 : a),
    (v2 == v3) -> (v1 == v2) = (v1 == v3).
Proof.
  intros.
  rewrite -> H1. (* why does the ssreflect rewriting tactic not work here. *)
  reflexivity.
Qed.

Lemma eq_replace_l : forall {a}`{EqLaws a} (v1 v2 v3 : a),
    (v2 == v3) -> (v2 == v1) = (v3 == v1).
Proof.
  intros.
  eapply Eq_m.
  eauto.
  eapply Eq_refl.
Qed.


(* Some cargo culting here. I'm not sure if we need to do all of this.*)

Local Lemma parametric_eq_trans : forall (a : Type) (H : Eq_ a),
  EqLaws a -> Transitive (fun x y : a => x == y).
Proof.
  intros.
  intros x y z.
  pose (k := Eq_trans).
  eapply k.
Defined. 

Local Lemma parametric_eq_sym : forall (a : Type) (H : Eq_ a),
  EqLaws a -> Symmetric (fun x y : a => x == y).
Proof.
  intros.
  intros x y.
  rewrite Eq_sym.
  auto.
Defined. 


Add Parametric Relation {a}`{H: EqLaws a} : a 
  (fun x y => x == y) 
    reflexivity proved by Eq_refl 
    symmetry proved by (@parametric_eq_sym a _ H)
    transitivity proved by (@parametric_eq_trans a _ H) as parametric_eq.

Instance: RewriteRelation (fun x y => x == y).


(* --------------------------------------------------------------------- *)


Ltac unfold_zeze :=
  repeat unfold op_zeze__, op_zeze____, 
  Eq_Int___,
  Eq_Integer___, 
  Eq_Word___,
  Eq_Char___,
  Eq_bool___, 
  Eq_unit___ ,
  Eq_comparison___, 
  Eq_pair___ , 
  Eq_list, 
  Eq___NonEmpty, Base.Eq___NonEmpty_op_zeze__,
  Eq___option, Base.Eq___option_op_zeze__.

Ltac unfold_zsze :=
  repeat unfold op_zsze__, op_zsze____,
  Eq_Int___,
  Eq_Integer___, 
  Eq_Word___,
  Eq_Char___,
  Eq_bool___,
  Eq_unit___ ,
  Eq_comparison___,
  Eq_pair___ ,
  Eq_list,
  Eq___NonEmpty,
  Eq___option.


Lemma simpl_option_some_eq a `{Eq_ a} (x y :a) :
  (Some x == Some y) = (x == y).
Proof.  
    repeat unfold Eq___option, op_zeze__, op_zeze____, 
           Base.Eq___option_op_zeze__, op_zeze____.
    auto.
Qed.

Lemma simpl_option_none_eq a `{Eq_ a} :
  ((None : option a) == None) = true.
Proof.  
    repeat unfold Eq___option, op_zeze__, op_zeze____, 
           Base.Eq___option_op_zeze__, op_zeze____.
    auto.
Qed.


Lemma simpl_list_cons_eq a `{Eq_ a} (x y :a) xs ys :
  (cons x xs) == (cons y ys) = (x == y) && (xs == ys).
Proof.  
    unfold op_zeze__, op_zeze____, Eq_list.
    simpl.
    auto.
Qed.

Lemma simpl_list_nil_eq a `{Eq_ a} :
  (nil : list a) == nil = true.
Proof.  
    unfold op_zeze__, op_zeze____, Eq_list.
    simpl.
    auto.
Qed.

Hint Rewrite @simpl_option_some_eq @simpl_option_none_eq 
             @simpl_list_cons_eq @simpl_list_nil_eq : hs_simpl.


(** ** [EqExact] **)
  
Class EqExact (t : Type) `{EqLaws t} :=
  { Eq_eq : forall x y : t, reflect (x = y) (x == y) }.

Theorem Neq_neq {t} `{EqExact t} (x y : t) : reflect (x <> y) (x /= y).
Proof. by rewrite Neq_inv; case CMP: (x == y) => /=; move/Eq_eq in CMP; constructor. Qed.

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
  unfold_zeze.
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
 unfold_zeze.
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
  - do 3 case=> [?|] //=; apply Eq_trans. (* COQ8.8: Why not `repeat'? *)
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

Instance EqLaws_pair {a b} `{EqLaws a} `{EqLaws b} : EqLaws (a * b).
Proof.
  split; rewrite /op_zeze__ /op_zsze__ /Eq_pair___ /op_zeze____ /op_zsze____.
  - case=> [??] //=. apply /andP; split; reflexivity.
  - do 2 case=> [??] //=. rewrite Eq_sym.
    apply andb_id2l=> Ha. rewrite Eq_sym =>//=.
  - do 3 case=> [??] //=. move /andP => [??] //= /andP => ?.
    apply /andP. intuition; eapply Eq_trans; eassumption.
  - do 2 case=> [??] //=. rewrite negb_involutive. reflexivity.
Qed.

Instance EqExact_pair {a b} `{EqExact a} `{EqExact b} : EqExact (a * b).
Proof.
  split; rewrite /op_zeze__ /op_zsze__ /Eq_pair___ /op_zeze____ /op_zsze____.
  case =>[??] [??] //=. destruct (_ == _) eqn:?.
  - rewrite andb_true_l. move /Eq_eq in Heqb0.
    destruct (_ == _) eqn:?.
    + constructor. move /Eq_eq in Heqb1. subst. reflexivity.
    + constructor. move /Eq_eq in Heqb1. intro. apply Heqb1.
      inversion H5; reflexivity.
  - rewrite andb_false_l. constructor. move /Eq_eq in Heqb0.
    intro. inversion H5. apply Heqb0. assumption.
Qed.

(* -------------------------------------------------------------------- *)


(* -------------------------------------------------------------------- *)

Class SemigroupLaws (t : Type) `{ Semigroup t } `{ EqLaws t } :=
  { semigroup_assoc    : forall (x y z : t), ((x <<>> (y <<>> z)) == ((x <<>> y) <<>> z)) = true;
  }.

Class MonoidLaws (t : Type) `{ Monoid t } `{SemigroupLaws t} `{ EqLaws t } :=
  { monoid_left_id  : forall x, (mappend mempty x == x) = true;
    monoid_right_id : forall x, (mappend x mempty == x) = true;
    monoid_semigroup : forall x y, (mappend x y == (x <<>> y)) = true;
    monoid_mconcat  : forall x, (mconcat x == foldr mappend mempty x) = true
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
   applicative_liftA2 : forall a b c (f : a -> b -> c) (x : t a) (y : t b),
     liftA2 f x y = (fmap f x <*> y);
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

(* We dropped Alternative
Class MonadPlusLaws (t : Type -> Type) `{!Functor t, !Applicative t, !Monad t, !Alternative t, !MonadPlus t, !FunctorLaws t, !ApplicativeLaws t, !MonadLaws t} :=
  { mzero_left : forall A B (f : A -> t B), (mzero >>= f)  =  mzero;
    mzero_right: forall A B (v : t A), (v >> mzero)   =  (mzero : t B);
    mplus_associative : forall A (f g h : t A),
          mplus f (mplus g h) = mplus (mplus f g) h;
  }.
*)


(* --------------------- Semigroup and Monoid ----------------------- *)

Instance instance_SemigroupLaws_unit : SemigroupLaws unit.
Proof.
  split;
    unfold op_zlzlzgzg__, Semigroup__unit, op_zlzlzgzg____,
         Base.Semigroup__unit_op_zlzlzgzg__.
  - intros. auto.
Qed.


Instance instance_MonoidLaws_unit : MonoidLaws unit.
Proof.
  split;
    unfold op_zlzlzgzg__, Semigroup__unit, op_zlzlzgzg____,
         Base.Semigroup__unit_op_zlzlzgzg__;
    unfold mappend, mempty, mconcat, Monoid__unit, mappend__,  mconcat__,
         Base.Monoid__unit_mappend,
         Base.Monoid__unit_mempty,
         Base.Monoid__unit_mconcat.
  - intro x. destruct x. auto.
  - intro x. destruct x. auto.
  - intros. auto.
  - intros x. induction x; simpl. auto. auto.
Qed.

Instance instance_SemigroupLaws_comparison : SemigroupLaws comparison.
Proof.
  split;
    unfold op_zlzlzgzg__, Semigroup__comparison, op_zlzlzgzg____,
      Base.Semigroup__comparison_op_zlzlzgzg__.
  - intros. destruct x; destruct y; apply Eq_refl.
Qed.

Instance instance_MonoidLaws_comparison : MonoidLaws comparison.
Proof.
  split;
    unfold op_zlzlzgzg__, Semigroup__comparison, op_zlzlzgzg____,
      Base.Semigroup__comparison_op_zlzlzgzg__;
    repeat unfold mappend, mempty, mconcat, instance_Monoid_comparison,
      Base.Monoid__comparison_mappend,
      Base.Monoid__comparison_mempty,
      Base.Monoid__comparison_mconcat.
  - intro x. apply Eq_refl.
  - intro x. destruct x; apply Eq_refl.
  - intros. apply Eq_refl.
  - intros x. induction x; apply Eq_refl.
Qed.

Instance instance_SemigroupLaws_option {a} `{ SemigroupLaws a } : SemigroupLaws (option a).
Proof.
  split;
    unfold op_zlzlzgzg__, Semigroup__option, op_zlzlzgzg____,
      Base.Semigroup__option_op_zlzlzgzg__.
  - intros x y z.
    destruct x; destruct y; destruct z; try apply Eq_refl.
    unfold op_zeze__, Eq___option, op_zeze____, Base.Eq___option_op_zeze__.
    apply semigroup_assoc.
Qed.

Instance instance_MonoidLaws_option {a} `{ MonoidLaws a } : MonoidLaws (option a).
Proof.
  split.
  - destruct x; apply Eq_refl.
  - destruct x; apply Eq_refl.
  - intros x y.
    destruct x; destruct y; try reflexivity; try apply Eq_refl.
  - induction x; simpl. auto.
    destruct a0; apply Eq_refl.
Qed.

Instance instance_SemigroupLaws_list {a} `{ EqLaws a } : SemigroupLaws (list a).
Proof.
  split; 
    unfold op_zlzlzgzg__, Semigroup__list, op_zlzlzgzg____,
      Base.Semigroup__list_op_zlzlzgzg__.
  - intros. apply Eq_reflI. apply app_assoc.
Qed.


Instance instance_MonoidLaws_list {a} `{ EqLaws a } : MonoidLaws (list a).
Proof.
  split.
  - intros. apply Eq_reflI. apply app_nil_l.
  - intros. apply Eq_reflI. apply app_nil_r.
  - intros. apply Eq_refl.
  - intros.
    apply Eq_reflI.
    induction x.
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
  - exact @map_id.
  - exact @map_map.
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
  - intros. destruct x, y; reflexivity.
  - reflexivity.
Qed.

Instance instance_ApplicativeLaws_list : ApplicativeLaws list.
Proof.
  split;
    repeat (unfold
      op_zlztzg__, liftA2, fmap,
      pure, Applicative__list,
      Base.Applicative__list_pure,
      Base.Applicative__list_op_zlztzg__,
      Functor__list,
      Base.Applicative__list_liftA2,
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
  - intros. rewrite !flat_map_concat_map !hs_coq_map List.map_map.
    reflexivity.
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
  - apply flat_map_cong => f1.
    by rewrite flat_map_cons_id.
Qed.

(* ------------------------------- boolean simplification ----------------------------- *)

(* The base edits file maps boolean operations to Coq's andb, orb, negb.

   We add some of the more common rewrites to the hs_simpl tactic so that they do not 
   need to be applied by hand.

 *)

Hint Rewrite andb_diag andb_false_r andb_true_r andb_false_l andb_true_l : hs_simpl.
Hint Rewrite orb_diag orb_false_r orb_true_r orb_false_l orb_true_l : hs_simpl.
Hint Rewrite negb_involutive : hs_simpl.

Hint Rewrite andb_true_iff orb_true_iff negb_true_iff negb_false_iff : hs_simpl.
