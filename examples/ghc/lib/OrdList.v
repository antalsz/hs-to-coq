(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
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

Inductive OrdList a : Type
  := None : OrdList a
  |  One : a -> OrdList a
  |  Many : list a -> OrdList a
  |  Cons : a -> (OrdList a) -> OrdList a
  |  Snoc : (OrdList a) -> a -> OrdList a
  |  Two : (OrdList a) -> (OrdList a) -> OrdList a.

Arguments None {_}.

Arguments One {_} _.

Arguments Many {_} _.

Arguments Cons {_} _ _.

Arguments Snoc {_} _ _.

Arguments Two {_} _ _.
(* Converted value declarations: *)

(* Translating `instance Outputable__OrdList' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

Definition appOL {a} : OrdList a -> OrdList a -> OrdList a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | None, b => b
    | a, None => a
    | One a, b => Cons a b
    | a, One b => Snoc a b
    | a, b => Two a b
    end.

Definition concatOL {a} : list (OrdList a) -> OrdList a :=
  fun aas => Data.Foldable.foldr appOL None aas.

Local Definition Semigroup__OrdList_op_zlzlzgzg__ {inst_a}
   : (OrdList inst_a) -> (OrdList inst_a) -> (OrdList inst_a) :=
  appOL.

Program Instance Semigroup__OrdList {a} : GHC.Base.Semigroup (OrdList a) :=
  fun _ k => k {| GHC.Base.op_zlzlzgzg____ := Semigroup__OrdList_op_zlzlzgzg__ |}.

Local Definition Monoid__OrdList_mconcat {inst_a}
   : list (OrdList inst_a) -> (OrdList inst_a) :=
  concatOL.

Local Definition Monoid__OrdList_mappend {inst_a}
   : (OrdList inst_a) -> (OrdList inst_a) -> (OrdList inst_a) :=
  _GHC.Base.<<>>_.

Definition consOL {a} : a -> OrdList a -> OrdList a :=
  fun a bs => Cons a bs.

Definition foldlOL {b} {a} : (b -> a -> b) -> b -> OrdList a -> b :=
  fix foldlOL arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, z, None => z
           | k, z, One x => k z x
           | k, z, Cons x xs => foldlOL k (k z x) xs
           | k, z, Snoc xs x => k (foldlOL k z xs) x
           | k, z, Two b1 b2 => foldlOL k (foldlOL k z b1) b2
           | k, z, Many xs => Data.Foldable.foldl k z xs
           end.

Definition foldrOL {a} {b} : (a -> b -> b) -> b -> OrdList a -> b :=
  fix foldrOL arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, z, None => z
           | k, z, One x => k x z
           | k, z, Cons x xs => k x (foldrOL k z xs)
           | k, z, Snoc xs x => foldrOL k (k x z) xs
           | k, z, Two b1 b2 => foldrOL k (foldrOL k z b2) b1
           | k, z, Many xs => Data.Foldable.foldr k z xs
           end.

Local Definition Foldable__OrdList_foldr
   : forall {a} {b}, (a -> b -> b) -> b -> OrdList a -> b :=
  fun {a} {b} => foldrOL.

Local Definition Foldable__OrdList_null : forall {a}, OrdList a -> bool :=
  fun {a} => Foldable__OrdList_foldr (fun arg_61__ arg_62__ => false) true.

Local Definition Foldable__OrdList_toList : forall {a}, OrdList a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      GHC.Base.build (fun _ arg_55__ arg_56__ =>
                        match arg_55__, arg_56__ with
                        | c, n => Foldable__OrdList_foldr c n t
                        end).

Local Definition Foldable__OrdList_foldl'
   : forall {b} {a}, (b -> a -> b) -> b -> OrdList a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => k GHC.Base.$! f z x
              end in
          Foldable__OrdList_foldr f' GHC.Base.id xs z0
      end.

Local Definition Foldable__OrdList_length
   : forall {a}, OrdList a -> GHC.Num.Int :=
  fun {a} =>
    Foldable__OrdList_foldl' (fun arg_64__ arg_65__ =>
                                match arg_64__, arg_65__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

Local Definition Foldable__OrdList_foldMap
   : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> OrdList a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} =>
    fun arg_1__ =>
      let 'f := arg_1__ in
      Foldable__OrdList_foldr (Coq.Program.Basics.compose GHC.Base.mappend f)
      GHC.Base.mempty.

Local Definition Foldable__OrdList_foldl
   : forall {b} {a}, (b -> a -> b) -> b -> OrdList a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                          (Foldable__OrdList_foldMap (Coq.Program.Basics.compose
                                                                      Data.SemigroupInternal.Mk_Dual
                                                                      (Coq.Program.Basics.compose
                                                                       Data.SemigroupInternal.Mk_Endo (GHC.Base.flip
                                                                        f))) t)) z
      end.

Local Definition Foldable__OrdList_foldr'
   : forall {a} {b}, (a -> b -> b) -> b -> OrdList a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => k GHC.Base.$! f x z
              end in
          Foldable__OrdList_foldl f' GHC.Base.id xs z0
      end.

Local Definition Foldable__OrdList_product
   : forall {a}, forall `{GHC.Num.Num a}, OrdList a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__OrdList_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__OrdList_sum
   : forall {a}, forall `{GHC.Num.Num a}, OrdList a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__OrdList_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__OrdList_fold
   : forall {m}, forall `{GHC.Base.Monoid m}, OrdList m -> m :=
  fun {m} `{GHC.Base.Monoid m} => Foldable__OrdList_foldMap GHC.Base.id.

Local Definition Foldable__OrdList_elem
   : forall {a}, forall `{GHC.Base.Eq_ a}, a -> OrdList a -> bool :=
  fun {a} `{GHC.Base.Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose Data.SemigroupInternal.getAny
                                                             (Foldable__OrdList_foldMap (Coq.Program.Basics.compose
                                                                                         Data.SemigroupInternal.Mk_Any
                                                                                         p))) _GHC.Base.==_.

Program Instance Foldable__OrdList : Data.Foldable.Foldable OrdList :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{GHC.Base.Eq_ a} =>
           Foldable__OrdList_elem ;
         Data.Foldable.fold__ := fun {m} `{GHC.Base.Monoid m} => Foldable__OrdList_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{GHC.Base.Monoid m} =>
           Foldable__OrdList_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__OrdList_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__OrdList_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__OrdList_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__OrdList_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__OrdList_length ;
         Data.Foldable.null__ := fun {a} => Foldable__OrdList_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__OrdList_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__OrdList_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__OrdList_toList |}.

Definition fromOL {a} : OrdList a -> list a :=
  fun a =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | None, acc => acc
                 | One a, acc => cons a acc
                 | Cons a b, acc => cons a (go b acc)
                 | Snoc a b, acc => go a (cons b acc)
                 | Two a b, acc => go a (go b acc)
                 | Many xs, acc => Coq.Init.Datatypes.app xs acc
                 end in
    go a nil.

Definition isNilOL {a} : OrdList a -> bool :=
  fun arg_0__ => match arg_0__ with | None => true | _ => false end.

Definition mapOL {a} {b} : (a -> b) -> OrdList a -> OrdList b :=
  fix mapOL arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, None => None
           | f, One x => One (f x)
           | f, Cons x xs => Cons (f x) (mapOL f xs)
           | f, Snoc xs x => Snoc (mapOL f xs) (f x)
           | f, Two x y => Two (mapOL f x) (mapOL f y)
           | f, Many xs => Many (GHC.Base.map f xs)
           end.

Local Definition Functor__OrdList_fmap
   : forall {a} {b}, (a -> b) -> OrdList a -> OrdList b :=
  fun {a} {b} => mapOL.

Local Definition Functor__OrdList_op_zlzd__
   : forall {a} {b}, a -> OrdList b -> OrdList a :=
  fun {a} {b} => fun x => Functor__OrdList_fmap (GHC.Base.const x).

Program Instance Functor__OrdList : GHC.Base.Functor OrdList :=
  fun _ k =>
    k {| GHC.Base.op_zlzd____ := fun {a} {b} => Functor__OrdList_op_zlzd__ ;
         GHC.Base.fmap__ := fun {a} {b} => Functor__OrdList_fmap |}.

Definition nilOL {a} : OrdList a :=
  None.

Local Definition Monoid__OrdList_mempty {inst_a} : (OrdList inst_a) :=
  nilOL.

Program Instance Monoid__OrdList {a} : GHC.Base.Monoid (OrdList a) :=
  fun _ k =>
    k {| GHC.Base.mappend__ := Monoid__OrdList_mappend ;
         GHC.Base.mconcat__ := Monoid__OrdList_mconcat ;
         GHC.Base.mempty__ := Monoid__OrdList_mempty |}.

Definition snocOL {a} : OrdList a -> a -> OrdList a :=
  fun as_ b => Snoc as_ b.

Definition toOL {a} : list a -> OrdList a :=
  fun arg_0__ => match arg_0__ with | nil => None | xs => Many xs end.

Local Definition Traversable__OrdList_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> OrdList a -> f (OrdList b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun f xs => toOL Data.Functor.<$> Data.Traversable.traverse f (fromOL xs).

Local Definition Traversable__OrdList_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, OrdList (f a) -> f (OrdList a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__OrdList_traverse GHC.Base.id.

Local Definition Traversable__OrdList_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, OrdList (m a) -> m (OrdList a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__OrdList_sequenceA.

Local Definition Traversable__OrdList_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> OrdList a -> m (OrdList b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__OrdList_traverse.

Program Instance Traversable__OrdList : Data.Traversable.Traversable OrdList :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
           Traversable__OrdList_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
           Traversable__OrdList_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
           Traversable__OrdList_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
           Traversable__OrdList_traverse |}.

Definition unitOL {a} : a -> OrdList a :=
  fun as_ => One as_.

(* External variables:
     bool cons false list nil true Coq.Init.Datatypes.app Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.elem__ Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.SemigroupInternal.Mk_Any
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getAny
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Semigroup
     GHC.Base.build GHC.Base.const GHC.Base.flip GHC.Base.fmap__ GHC.Base.id
     GHC.Base.map GHC.Base.mappend GHC.Base.mappend__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.op_zdzn__ GHC.Base.op_zeze__
     GHC.Base.op_zlzd____ GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Num.Int
     GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
