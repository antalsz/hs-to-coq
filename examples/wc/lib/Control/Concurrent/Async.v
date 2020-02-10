(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import ITree.Itree.

(* Converted imports: *)

Require Data.Either.
Require Import Data.Functor.
Require Import GHC.Base.
Require IO.

(* Converted type declarations: *)

Inductive Concurrently a : Type
  := | MkConcurrently (runConcurrently : IO.IO a) : Concurrently a.

Arguments MkConcurrently {_} _.

Definition runConcurrently {a} (arg_0__ : Concurrently a) :=
  let 'MkConcurrently runConcurrently := arg_0__ in
  runConcurrently.

(* Converted value declarations: *)

Definition concurrently {a} {b} : IO.IO a -> IO.IO b -> IO.IO (a * b)%type :=
  fun left_ right_ =>
    let fix collect arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | cons (Data.Either.Left a) (cons (Data.Either.Right b) nil), _ =>
                     return_ (pair a b)
                 | cons (Data.Either.Right b) (cons (Data.Either.Left a) nil), _ =>
                     return_ (pair a b)
                 | xs, m =>
                     m >>=
                     (fun e =>
                        match e with
                        | Data.Either.Left ex => GHC.IO.throwIO ex
                        | Data.Either.Right r => collect (cons r xs) m
                        end)
                 end in
    concurrently' left_ right_ (collect nil).

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Concurrent.Async.Show__AsyncCancelled' *)

Local Definition Eq___AsyncCancelled_op_zeze__
   : AsyncCancelled -> AsyncCancelled -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | AsyncCancelled, AsyncCancelled => true
    end.

Local Definition Eq___AsyncCancelled_op_zsze__
   : AsyncCancelled -> AsyncCancelled -> bool :=
  fun x y => negb (Eq___AsyncCancelled_op_zeze__ x y).

Program Instance Eq___AsyncCancelled : Eq_ AsyncCancelled :=
  fun _ k__ =>
    k__ {| op_zeze____ := Eq___AsyncCancelled_op_zeze__ ;
           op_zsze____ := Eq___AsyncCancelled_op_zsze__ |}.

(* Skipping instance `Control.Concurrent.Async.Functor__Async' of class
   `GHC.Base.Functor' *)

(* Skipping all instances of class `Data.Hashable.Class.Hashable', including
   `Control.Concurrent.Async.Hashable__Async' *)

(* Skipping instance `Control.Concurrent.Async.Ord__Async' of class
   `GHC.Base.Ord' *)

Local Definition Eq___Async_op_zeze__ {inst_a}
   : (Async inst_a) -> (Async inst_a) -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Async a _, Async b _ => a == b
    end.

Local Definition Eq___Async_op_zsze__ {inst_a}
   : (Async inst_a) -> (Async inst_a) -> bool :=
  fun x y => negb (Eq___Async_op_zeze__ x y).

Program Instance Eq___Async {a} : Eq_ (Async a) :=
  fun _ k__ =>
    k__ {| op_zeze____ := Eq___Async_op_zeze__ ;
           op_zsze____ := Eq___Async_op_zsze__ |}.

(* Skipping all instances of class `GHC.Exception.Exception', including
   `Control.Concurrent.Async.Exception__AsyncCancelled' *)

(* Skipping all instances of class `GHC.Exception.Exception', including
   `Control.Concurrent.Async.Exception__ExceptionInLinkedThread' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Concurrent.Async.Show__ExceptionInLinkedThread' *)

Local Definition Monoid__Concurrently_mappend {inst_a} `{Semigroup inst_a}
  `{Monoid inst_a}
   : (Concurrently inst_a) -> (Concurrently inst_a) -> (Concurrently inst_a) :=
  _<<>>_.

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

Local Definition Semigroup__Concurrently_op_zlzlzgzg__ {inst_a} `{Semigroup
  inst_a}
   : (Concurrently inst_a) -> (Concurrently inst_a) -> (Concurrently inst_a) :=
  liftA2 _<<>>_.

Program Instance Semigroup__Concurrently {a} `{Semigroup a}
   : Semigroup (Concurrently a) :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__Concurrently_op_zlzlzgzg__ |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Concurrent.Async.Alternative__Concurrently' *)

Local Definition Applicative__Concurrently_op_zlztzg__
   : forall {a} {b}, Concurrently (a -> b) -> Concurrently a -> Concurrently b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | MkConcurrently fs, MkConcurrently as_ =>
          MkConcurrently ((fun '(pair f a) => f a) <$> concurrently fs as_)
      end.

Local Definition Applicative__Concurrently_liftA2
   : forall {a} {b} {c},
     (a -> b -> c) -> Concurrently a -> Concurrently b -> Concurrently c :=
  fun {a} {b} {c} => fun f x => Applicative__Concurrently_op_zlztzg__ (fmap f x).

Local Definition Applicative__Concurrently_op_ztzg__
   : forall {a} {b}, Concurrently a -> Concurrently b -> Concurrently b :=
  fun {a} {b} => fun a1 a2 => Applicative__Concurrently_op_zlztzg__ (id <$ a1) a2.

Local Definition Applicative__Concurrently_pure
   : forall {a}, a -> Concurrently a :=
  fun {a} => MkConcurrently ∘ return_.

Program Instance Applicative__Concurrently : Applicative Concurrently :=
  fun _ k__ =>
    k__ {| liftA2__ := fun {a} {b} {c} => Applicative__Concurrently_liftA2 ;
           op_zlztzg____ := fun {a} {b} => Applicative__Concurrently_op_zlztzg__ ;
           op_ztzg____ := fun {a} {b} => Applicative__Concurrently_op_ztzg__ ;
           pure__ := fun {a} => Applicative__Concurrently_pure |}.

Local Definition Functor__Concurrently_fmap
   : forall {a} {b}, (a -> b) -> Concurrently a -> Concurrently b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkConcurrently a => MkConcurrently (f <$> a)
      end.

Local Definition Functor__Concurrently_op_zlzd__
   : forall {a} {b}, a -> Concurrently b -> Concurrently a :=
  fun {a} {b} => Functor__Concurrently_fmap ∘ const.

Program Instance Functor__Concurrently : Functor Concurrently :=
  fun _ k__ =>
    k__ {| fmap__ := fun {a} {b} => Functor__Concurrently_fmap ;
           op_zlzd____ := fun {a} {b} => Functor__Concurrently_op_zlzd__ |}.

(* External variables:
     Applicative Async AsyncCancelled Eq_ Functor Monoid Semigroup bool concurrently'
     cons const fmap fmap__ foldr id liftA2 liftA2__ list mappend__ mconcat__ mempty
     mempty__ negb nil op_z2218U__ op_zeze__ op_zeze____ op_zgzgze__ op_zlzd__
     op_zlzd____ op_zlzdzg__ op_zlzlzgzg__ op_zlzlzgzg____ op_zlztzg____ op_zsze____
     op_zt__ op_ztzg____ pair pure pure__ return_ true Data.Either.Left
     Data.Either.Right GHC.IO.throwIO IO.IO
*)
