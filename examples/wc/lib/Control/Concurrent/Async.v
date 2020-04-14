(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import ITree.ITree.

(* Converted imports: *)

Require Import Data.Functor.
Require Import Data.Traversable.
Require Import GHC.Base.
Require IO.

(* Converted type declarations: *)

Inductive Concurrently a : Type
  := | MkConcurrently (runConcurrently : IO.IO a) : Concurrently a.

Arguments MkConcurrently {_} _.

Polymorphic Definition runConcurrently {a} (arg_0__ : Concurrently a) :=
  let 'MkConcurrently runConcurrently := arg_0__ in
  runConcurrently.

(* Converted value declarations: *)

Polymorphic Definition concurrently {a b : Type} : IO.IO a -> IO.IO b -> IO.IO (a * b) :=
  embed IO.Concurrently.

Local Polymorphic Definition Functor__Concurrently_fmap
   : forall {a} {b}, (a -> b) -> Concurrently a -> Concurrently b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkConcurrently a => MkConcurrently (f <$> a)
      end.

Local Polymorphic Definition Functor__Concurrently_op_zlzd__
   : forall {a} {b}, a -> Concurrently b -> Concurrently a :=
  fun {a} {b} => Functor__Concurrently_fmap ∘ const.

Polymorphic Program Instance Functor__Concurrently : Functor Concurrently :=
  fun _ k__ =>
    k__ {| fmap__ := fun {a} {b} => Functor__Concurrently_fmap ;
           op_zlzd____ := fun {a} {b} => Functor__Concurrently_op_zlzd__ |}.

Local Polymorphic Definition Applicative__Concurrently_op_zlztzg__
   : forall {a} {b}, Concurrently (a -> b) -> Concurrently a -> Concurrently b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | MkConcurrently fs, MkConcurrently as_ =>
          MkConcurrently ((fun '(pair f a) => f a) <$> concurrently fs as_)
      end.

Local Polymorphic Definition Applicative__Concurrently_liftA2
   : forall {a} {b} {c},
     (a -> b -> c) -> Concurrently a -> Concurrently b -> Concurrently c :=
  fun {a} {b} {c} => fun f x => Applicative__Concurrently_op_zlztzg__ (fmap f x).

Local Polymorphic Definition Applicative__Concurrently_op_ztzg__
   : forall {a} {b}, Concurrently a -> Concurrently b -> Concurrently b :=
  fun {a} {b} => fun a1 a2 => Applicative__Concurrently_op_zlztzg__ (id <$ a1) a2.

Local Polymorphic Definition Applicative__Concurrently_pure
   : forall {a}, a -> Concurrently a :=
  fun {a} => MkConcurrently ∘ return_.

Polymorphic Program Instance Applicative__Concurrently : Applicative Concurrently :=
  fun _ k__ =>
    k__ {| liftA2__ := fun {a} {b} {c} => Applicative__Concurrently_liftA2 ;
           op_zlztzg____ := fun {a} {b} => Applicative__Concurrently_op_zlztzg__ ;
           op_ztzg____ := fun {a} {b} => Applicative__Concurrently_op_ztzg__ ;
           pure__ := fun {a} => Applicative__Concurrently_pure |}.

Local Definition Semigroup__Concurrently_op_zlzlzgzg__ {inst_a} `{Semigroup
  inst_a}
   : (Concurrently inst_a) -> (Concurrently inst_a) -> (Concurrently inst_a) :=
  liftA2 _<<>>_.

Program Instance Semigroup__Concurrently {a} `{Semigroup a}
   : Semigroup (Concurrently a) :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__Concurrently_op_zlzlzgzg__ |}.

Local Definition Monoid__Concurrently_mappend {inst_a} `{Semigroup inst_a}
  `{Monoid inst_a}
   : (Concurrently inst_a) -> (Concurrently inst_a) -> (Concurrently inst_a) :=
  _<<>>_.

Polymorphic Definition mapConcurrently {t} {a} {b} `{Traversable t}
   : (a -> IO.IO b) -> t a -> IO.IO (t b) :=
  fun f => runConcurrently ∘ traverse (MkConcurrently ∘ f).

Polymorphic Definition forConcurrently {t} {a} {b} `{Traversable t}
   : t a -> (a -> IO.IO b) -> IO.IO (t b) :=
  flip mapConcurrently.

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Concurrent.Async.Show__AsyncCancelled' *)

(* Skipping instance `Control.Concurrent.Async.Eq___AsyncCancelled' of class
   `GHC.Base.Eq_' *)

(* Skipping instance `Control.Concurrent.Async.Functor__Async' of class
   `GHC.Base.Functor' *)

(* Skipping all instances of class `Data.Hashable.Class.Hashable', including
   `Control.Concurrent.Async.Hashable__Async' *)

(* Skipping instance `Control.Concurrent.Async.Ord__Async' of class
   `GHC.Base.Ord' *)

(* Skipping instance `Control.Concurrent.Async.Eq___Async' of class
   `GHC.Base.Eq_' *)

(* Skipping all instances of class `GHC.Exception.Exception', including
   `Control.Concurrent.Async.Exception__AsyncCancelled' *)

(* Skipping all instances of class `GHC.Exception.Exception', including
   `Control.Concurrent.Async.Exception__ExceptionInLinkedThread' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Concurrent.Async.Show__ExceptionInLinkedThread' *)

Local Definition Monoid__Concurrently_mempty {inst_a} `{Semigroup inst_a}
  `{Monoid inst_a}
   : (Concurrently inst_a) :=
  pure mempty.

Local Definition Monoid__Concurrently_mconcat {inst_a} `{Semigroup inst_a}
  `{Monoid inst_a}
   : list (Concurrently inst_a) -> (Concurrently inst_a) :=
  foldr Monoid__Concurrently_mappend Monoid__Concurrently_mempty.

Program Instance Monoid__Concurrently {a} `{Semigroup a} `{Monoid a}
   : Monoid (Concurrently a) :=
  fun _ k__ =>
    k__ {| mappend__ := Monoid__Concurrently_mappend ;
           mconcat__ := Monoid__Concurrently_mconcat ;
           mempty__ := Monoid__Concurrently_mempty |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Concurrent.Async.Alternative__Concurrently' *)

(* External variables:
     Applicative Functor Monoid Semigroup Traversable Type const embed flip fmap
     fmap__ foldr id liftA2 liftA2__ list mappend__ mconcat__ mempty mempty__
     op_z2218U__ op_zlzd__ op_zlzd____ op_zlzdzg__ op_zlzlzgzg__ op_zlzlzgzg____
     op_zlztzg____ op_zt__ op_ztzg____ pair pure pure__ return_ traverse
     IO.Concurrently IO.IO
*)
