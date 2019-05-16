From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq ssrnum ssralg rat bigop.
Set Bullet Behavior "Strict Subproofs".

Require Import Coq.Lists.List.

Require Import GHC.Base.     Import GHC.Base.Notations.
Require Import GHC.Num.      Import GHC.Num.Notations.
Require Import Data.Functor. Import Data.Functor.Notations.
Require Import Data.Foldable.

Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Foldable.

Require Import Control.Monad.Random.Class.
Require Import Data.List.Shuffle.

Theorem riffle_eq {m a} `{MonadRandom m} (xs0 : list a) (nx0 : Int) (ys0 : list a) (ny0 : Int) :
  riffle xs0 nx0 ys0 ny0 =
    match xs0 , nx0 , ys0 , ny0 with
    | xs,      _,  nil,     _  => pure xs
    | nil,     _,  ys,      _  => pure ys
    | x :: xs, nx, y :: ys, ny =>
      getRandomR (pair #1 (nx + ny)) >>= fun k =>
        if k <= nx
        then cons x <$> riffle xs (nx - #1) (y :: ys) ny
        else cons y <$> riffle (x :: xs) nx ys (ny - #1)
    end.
Proof.
Admitted.

Open Scope ring_scope.

(* riffle *)
(* halve *)
(* shuffleLength *)
(* shuffle *)

Theorem halve_In {a : eqType} (zs : list a) (e : a) :
  let: (xs, ys) := halve zs
  in In e zs <-> In e xs \/ In e ys.
Proof.
  elim: zs => [|z zs IH] /=; first tauto.
  case: (halve zs) IH => [xs ys] IH /=.
  tauto.
Qed.

Theorem halve_in {a : eqType} (zs : list a) (e : a) :
  let: (xs, ys) := halve zs
  in e \in zs = (e \in xs) || (e \in ys).
Proof.
  elim: zs => [|z zs IH] /=; first tauto.
  case: (halve zs) IH => [xs ys] IH /=.
  by rewrite !inE IH orbAC orbA.
Qed.

Inductive Unique {a} : list a -> Prop :=
| UNil       : Unique [::]
| UCons x xs : ~ (In x xs) -> Unique xs -> Unique (x :: xs).

Require Import Coq.Logic.FunctionalExtensionality.

Theorem Unique_hprop {a} (xs : list a) (u v : Unique xs) :
  u = v.
Proof.
  elim: xs u v => [|x xs IH] u v.
  - refine (match u as u' in Unique xs_u , v as v' in Unique xs_v
              return forall (pf_u : xs_u = [::]) (pf_v : xs_v = [::]),
                       eq_rect xs_u Unique u' _ pf_u = u ->
                       eq_rect xs_v Unique v' _ pf_v = v ->
                       u = v
            with
            | UNil , UNil => _
            | _    , _    => _
            end erefl erefl erefl erefl);
      intros pf_u pf_v; try solve [inversion pf_u | inversion pf_v].
    move=> <- <- {u v}.
    f_equal.
    admit.
    
  - refine (match u as u' in Unique xxs_u , v as v' in Unique xxs_v
              return forall (pf_u : xxs_u = x :: xs) (pf_v : xxs_v = x :: xs),
                       eq_rect xxs_u Unique u' _ pf_u = u ->
                       eq_rect xxs_v Unique v' _ pf_v = v ->
                       u = v
            with
            | UCons x_u xs_u nin_u uniq_u , UCons x_v xs_v nin_v uniq_v => _
            | _                           , _                           => _
            end erefl erefl erefl erefl);
      intros pf_u pf_v; try solve [inversion pf_u | inversion pf_v].
    inversion pf_u; inversion pf_v; subst x_u xs_u x_v xs_v.
    move=> <- <- {u v}.
    f_equal.
    + rewrite (IH uniq_u uniq_v); f_equal.
      by apply functional_extensionality.
    + admit.
Qed.

Require Import Coq.Program.Equality.

Theorem Unique_hprop {a} (xs : list a) (u v : Unique xs) :
  u = v.
Proof.
  elim: xs u v => [|x xs IH] u v.
  - by dependent destruction u; dependent destruction v.
  - dependent destruction u; dependent destruction v.
    f_equal; last apply IH.
    by apply functional_extensionality.
Qed.

Record Distribution a := {
  events        : list a
  probabilities : a -> rat
  unique        :

Class MonadRandomLaws m `{MonadRandom m} := {
  events             {a}                            : m a -> list a;
  probability        {a}                            : m a -> a -> rat;
  probability_01     {a}   (p : m a) (x : a)        : 0 <= probability p x <= 1;
  probability_events {a}   (p : m a) (x : a)        : In x (events p) <-> probability p x <> 0;
  probability_sum    {a}   (p : m a)                : \sum_(x <- events p) probability p x = 1;
  events_pure        {a}   (x : a)                  : events (pure x) = [:: x];
  events_bind        {a b} (p : m a) (f : a -> m b) : events (p >>= f) = (events p >>= events ∘ f)
  (* probability_bind   {a b} (p : m a) (f : a -> m b) (x : b) : probability (p >>= f) x = \sum_(e <- events p | y <- events (f e) | y = x) probability (f e) y *)
}.

Inductive Interleaved {a} : list a -> list a -> list a -> Prop :=
| Interleaved_nil              :                         Interleaved [::]      [::]      [::]
| Interleaved_left  z xs ys zs : Interleaved xs ys zs -> Interleaved (z :: xs) ys        (z :: zs)
| Interleaved_right z xs ys zs : Interleaved xs ys zs -> Interleaved xs        (z :: ys) (z :: zs).
Hint Constructors Interleaved.

Lemma interleaved_comm {a} (xs ys zs : list a) :
  Interleaved xs ys zs -> Interleaved ys xs zs.
Proof.
  induction 1 as [ | z xs ys zs INT IH  | z xs ys zs INT IH ].
  all: by [constructor; apply IH |].
Qed.
Hint Resolve interleaved_comm.

Lemma interleaved_idr {a} (xs : list a) :
  Interleaved xs [::] xs.
Proof.
  elim: xs => [|x xs IH]; first done.
  constructor; apply IH.
Qed.
Hint Resolve interleaved_idr.

Lemma interleaved_idl {a} (ys : list a) :
  Interleaved [::] ys ys.
Proof. auto. Qed.
Hint Resolve interleaved_idl.

Lemma interleaved_nil_r {a} (xs xs' : list a) :
  Interleaved xs [::] xs' -> xs = xs'.
Proof.
  remember [::] as NIL eqn:def_NIL => INT.
  move: def_NIL; induction INT as [ | x xs NIL' xs' INT IH | x xs NIL' xs' INT IH ]; try done.
  by move=> /IH ->.
Qed.
Hint Resolve interleaved_nil_r.

Lemma interleaved_nil_l {a} (ys ys' : list a) :
  Interleaved [::] ys ys' -> ys = ys'.
Proof. auto. Qed.
Hint Resolve interleaved_nil_l.

Lemma interleaved_iff_nil_r {a} (xs xs' : list a) :
  Interleaved xs [::] xs' <-> xs = xs'.
Proof. split; last move=> ->; auto. Qed.
Hint Resolve interleaved_iff_nil_r.

Lemma interleaved_iff_nil_l {a} (ys ys' : list a) :
  Interleaved [::] ys ys' <-> ys = ys'.
Proof. split; last move=> ->; auto. Qed.
Hint Resolve interleaved_iff_nil_l.

Lemma interleaved_length {a} (xs ys zs : list a) :
  Interleaved xs ys zs -> length zs = (length xs + length ys)%Z.
Proof.
  induction 1 as [ | z xs ys zs INT IH  | z xs ys zs INT IH ]; move=> //; hs_simpl.
  - by rewrite IH Z.add_succ_l.
  - by rewrite IH Z.add_succ_r.
Qed.

Lemma interleaved_refl_nil {a} (xs : list a) :
  Interleaved xs xs xs -> xs = [::].
Proof.
  move=> /interleaved_length.
  rewrite hs_coq_length_list !Zlength_correct -Nat2Z.inj_add Nat2Z.inj_iff /=.
  case: xs => [|x xs] //=.
  omega.
Qed.

Lemma interleaved_In_iff {a} (xs ys zs : list a) :
  Interleaved xs ys zs ->
  forall z, In z zs <-> In z xs \/ In z ys.
Proof.
  induction 1 as [ | x xs ys zs INT IH  | y xs ys zs INT IH ]; move=> /= z.
  all: rewrite ?IH; tauto.
Qed.
Hint Resolve interleaved_In_iff.

Lemma interleaved_In_or {a} (xs ys zs : list a) :
  Interleaved xs ys zs ->
  forall z, In z zs -> In z xs \/ In z ys.
Proof.
  induction 1 as [ | x xs ys zs INT IH  | y xs ys zs INT IH ]; move=> //= z.
  all: move=> [|/IH]; tauto.
Qed.
Hint Resolve interleaved_In_or.

Lemma interleaved_left_In {a} (xs ys zs : list a) :
  Interleaved xs ys zs ->
  forall z, In z xs -> In z zs.
Proof.
  induction 1 as [ | x xs ys zs INT IH  | y xs ys zs INT IH ]; move=> //= z.
  - move=> [|/IH]; tauto.
  - move=> /IH; tauto.
Qed.
Hint Resolve interleaved_left_In.

Lemma interleaved_right_In {a} (xs ys zs : list a) :
  Interleaved xs ys zs ->
  forall z, In z ys -> In z zs.
Proof. eauto. Qed.

Theorem riffle_riffled {m a} `{MonadRandomLaws m} (xs : list a) nx ys ny :
  length xs = nx ->
  length ys = ny ->
  forall zs, In zs (events (riffle xs nx ys ny)) <-> Interleaved xs ys zs.
Proof.
  elim: xs nx ny => [|x xs IH] //= nx ny; hs_simpl.
  - move=> <- <- zs /=.
    rewrite riffle_eq /= interleaved_iff_nil_l.
    case: ys => [|y ys] //=; rewrite events_pure /=; tauto.
  - move=> <- <- zs /=.
    rewrite riffle_eq /=; case: ys IH => [|y ys] IH.
    + rewrite events_pure /= interleaved_iff_nil_r; tauto.
    + 
