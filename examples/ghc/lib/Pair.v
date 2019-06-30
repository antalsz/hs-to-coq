(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Pair a : Type := | Mk_Pair (pFst : a) (pSnd : a) : Pair a.

Arguments Mk_Pair {_} _ _.

Definition pFst {a} (arg_0__ : Pair a) :=
  let 'Mk_Pair pFst _ := arg_0__ in
  pFst.

Definition pSnd {a} (arg_0__ : Pair a) :=
  let 'Mk_Pair _ pSnd := arg_0__ in
  pSnd.

(* Converted value declarations: *)

Definition unPair {a} : Pair a -> (a * a)%type :=
  fun '(Mk_Pair x y) => pair x y.

Definition toPair {a} : (a * a)%type -> Pair a :=
  fun '(pair x y) => Mk_Pair x y.

Definition swap {a} : Pair a -> Pair a :=
  fun '(Mk_Pair x y) => Mk_Pair y x.

Definition pLiftSnd {a} : (a -> a) -> Pair a -> Pair a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_Pair a b => Mk_Pair a (f b)
    end.

Definition pLiftFst {a} : (a -> a) -> Pair a -> Pair a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_Pair a b => Mk_Pair (f a) b
    end.

(* Skipping all instances of class `Outputable.Outputable', including
   `Pair.Outputable__Pair' *)

Local Definition Semigroup__Pair_op_zlzlzgzg__ {inst_a} `{GHC.Base.Semigroup
  inst_a}
   : (Pair inst_a) -> (Pair inst_a) -> (Pair inst_a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Pair a1 b1, Mk_Pair a2 b2 =>
        Mk_Pair (a1 GHC.Base.<<>> a2) (b1 GHC.Base.<<>> b2)
    end.

Program Instance Semigroup__Pair {a} `{GHC.Base.Semigroup a}
   : GHC.Base.Semigroup (Pair a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__Pair_op_zlzlzgzg__ |}.

Local Definition Monoid__Pair_mappend {inst_a} `{GHC.Base.Semigroup inst_a}
  `{GHC.Base.Monoid inst_a}
   : (Pair inst_a) -> (Pair inst_a) -> (Pair inst_a) :=
  _GHC.Base.<<>>_.

Local Definition Monoid__Pair_mempty {inst_a} `{GHC.Base.Semigroup inst_a}
  `{GHC.Base.Monoid inst_a}
   : (Pair inst_a) :=
  Mk_Pair GHC.Base.mempty GHC.Base.mempty.

Local Definition Monoid__Pair_mconcat {inst_a} `{GHC.Base.Semigroup inst_a}
  `{GHC.Base.Monoid inst_a}
   : list (Pair inst_a) -> (Pair inst_a) :=
  GHC.Base.foldr Monoid__Pair_mappend Monoid__Pair_mempty.

Program Instance Monoid__Pair {a} `{GHC.Base.Semigroup a} `{GHC.Base.Monoid a}
   : GHC.Base.Monoid (Pair a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__Pair_mappend ;
           GHC.Base.mconcat__ := Monoid__Pair_mconcat ;
           GHC.Base.mempty__ := Monoid__Pair_mempty |}.

Local Definition Traversable__Pair_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> Pair a -> f (Pair b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Pair x y => (Mk_Pair Data.Functor.<$> f x) GHC.Base.<*> f y
      end.

Local Definition Traversable__Pair_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Pair a -> m (Pair b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Pair_traverse.

Local Definition Traversable__Pair_sequenceA
   : forall {f} {a}, forall `{GHC.Base.Applicative f}, Pair (f a) -> f (Pair a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Pair_traverse GHC.Base.id.

Local Definition Traversable__Pair_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, Pair (m a) -> m (Pair a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Pair_sequenceA.

Local Definition Foldable__Pair_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> Pair a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Pair x y => GHC.Base.mappend (f x) (f y)
      end.

Local Definition Foldable__Pair_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, Pair m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__Pair_foldMap GHC.Base.id.

Local Definition Foldable__Pair_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> Pair a -> b :=
  fun {b} {a} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Pair_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

Local Definition Foldable__Pair_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> Pair a -> b :=
  fun {a} {b} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Pair_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Pair_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> Pair a -> b :=
  fun {b} {a} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Pair_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Pair_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> Pair a -> b :=
  fun {a} {b} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Pair_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Pair_length : forall {a}, Pair a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__Pair_foldl' (fun arg_0__ arg_1__ =>
                             match arg_0__, arg_1__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

Local Definition Foldable__Pair_null : forall {a}, Pair a -> bool :=
  fun {a} => Foldable__Pair_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Pair_product
   : forall {a}, forall `{GHC.Num.Num a}, Pair a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Pair_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Pair_sum
   : forall {a}, forall `{GHC.Num.Num a}, Pair a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Pair_foldMap
                                Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Pair_toList : forall {a}, Pair a -> list a :=
  fun {a} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Pair_foldr c n t)).

Program Instance Foldable__Pair : Data.Foldable.Foldable Pair :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} =>
             Foldable__Pair_fold ;
           Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
             Foldable__Pair_foldMap ;
           Data.Foldable.foldl__ := fun {b} {a} => Foldable__Pair_foldl ;
           Data.Foldable.foldl'__ := fun {b} {a} => Foldable__Pair_foldl' ;
           Data.Foldable.foldr__ := fun {a} {b} => Foldable__Pair_foldr ;
           Data.Foldable.foldr'__ := fun {a} {b} => Foldable__Pair_foldr' ;
           Data.Foldable.length__ := fun {a} => Foldable__Pair_length ;
           Data.Foldable.null__ := fun {a} => Foldable__Pair_null ;
           Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} => Foldable__Pair_product ;
           Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__Pair_sum ;
           Data.Foldable.toList__ := fun {a} => Foldable__Pair_toList |}.

Local Definition Functor__Pair_fmap
   : forall {a} {b}, (a -> b) -> Pair a -> Pair b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Pair x y => Mk_Pair (f x) (f y)
      end.

Local Definition Functor__Pair_op_zlzd__
   : forall {a} {b}, a -> Pair b -> Pair a :=
  fun {a} {b} => Functor__Pair_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Pair : GHC.Base.Functor Pair :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a} {b} => Functor__Pair_fmap ;
           GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Pair_op_zlzd__ |}.

Program Instance Traversable__Pair : Data.Traversable.Traversable Pair :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__Pair_mapM ;
           Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
             Traversable__Pair_sequence ;
           Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Pair_sequenceA ;
           Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Pair_traverse |}.

Local Definition Applicative__Pair_op_zlztzg__
   : forall {a} {b}, Pair (a -> b) -> Pair a -> Pair b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Pair f g, Mk_Pair x y => Mk_Pair (f x) (g y)
      end.

Local Definition Applicative__Pair_liftA2
   : forall {a} {b} {c}, (a -> b -> c) -> Pair a -> Pair b -> Pair c :=
  fun {a} {b} {c} => fun f x => Applicative__Pair_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Pair_op_ztzg__
   : forall {a} {b}, Pair a -> Pair b -> Pair b :=
  fun {a} {b} =>
    fun a1 a2 => Applicative__Pair_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Pair_pure : forall {a}, a -> Pair a :=
  fun {a} => fun x => Mk_Pair x x.

Program Instance Applicative__Pair : GHC.Base.Applicative Pair :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a} {b} {c} => Applicative__Pair_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Pair_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Pair_op_ztzg__ ;
           GHC.Base.pure__ := fun {a} => Applicative__Pair_pure |}.

(* External variables:
     bool false list op_zt__ pair true Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap__ Data.Foldable.fold__
     Data.Foldable.foldl'__ Data.Foldable.foldl__ Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse__ GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.Semigroup GHC.Base.build' GHC.Base.const GHC.Base.flip
     GHC.Base.fmap GHC.Base.fmap__ GHC.Base.foldr GHC.Base.id GHC.Base.liftA2__
     GHC.Base.mappend GHC.Base.mappend__ GHC.Base.mconcat__ GHC.Base.mempty
     GHC.Base.mempty__ GHC.Base.op_z2218U__ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Base.op_zlztzg__
     GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure__ GHC.Num.Int
     GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
