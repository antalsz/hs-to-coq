Require Import ITree.ITree.
From ExtLib.Structures Require Functor Applicative.

Set Printing Universes.

(** [Functor] type class from [hs-to-coq]. *)

Record Functor__Dict f := Functor__Dict_Build {
  fmap__ : forall {a} {b}, (a -> b) -> f a -> f b ;
  op_zlzd____ : forall {a} {b}, a -> f b -> f a }.

Definition Functor f :=
  forall r__, (Functor__Dict f -> r__) -> r__.
Existing Class Functor.


(** An effect functor which contains [itree]. *)

Inductive FooE : Type -> Type :=
| ApE {A B} : itree FooE A -> itree FooE B -> FooE (A * B).

Print FooE.
(** This gives you:
    itreeF.u1 < ITree.Core.ITreeDefinition.2
 *)

Definition apE {A B} : itree FooE A -> itree FooE B -> itree FooE (A * B) :=
  embed ApE.
  
Inductive Foo A :=
| MkFoo : itree FooE A -> Foo A.

Arguments MkFoo {_}.


Definition Foo__fmap {A B} : (A -> B) -> Foo A -> Foo B.
  intros f x. destruct x. constructor.
  apply (Functor.fmap f i).
Defined.

Definition const {a} {b} : a -> b -> a :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | x, _ => x end.

Definition op_z2218U__ {b} {c} {a} : (b -> c) -> (a -> b) -> a -> c :=
  fun f g => fun x => f (g x).
  
Definition Foo__zlzd {A B : Type} : A -> Foo B -> Foo A := op_z2218U__ Foo__fmap const.


Program Instance Functor__Foo : Functor Foo :=
  fun _ k__ =>
    k__ {| fmap__ := fun {a} {b} => Foo__fmap;
           op_zlzd____ := fun {a} {b} => Foo__zlzd |}.

Definition Foo__ap {A B} (f : Foo (A -> B)) (a : Foo A) : Foo B :=
  match f, a with
  | MkFoo f', MkFoo a' =>
    MkFoo (Functor.fmap (fun '(pair f a) => f a) (apE f' a'))
  end.

Definition Foo__liftA2 {A B C} (f : A -> B -> C) (x : Foo A) (y : Foo B) : Foo C :=
  Foo__ap (Foo__fmap f x) y.

Definition Foo__pure {A} x : Foo A := MkFoo (Ret x).

Definition op_zlzd__ {f} `{g__0__ : Functor f} : forall {a} {b}, a -> f b -> f a :=
  g__0__ _ (op_zlzd____ f).

Definition Foo__ztzg {A B} (x : Foo A) (y : Foo B) : Foo B :=
  Foo__ap (op_zlzd__ id x) y.

(** A failed approach. We will show a working approach later. *)
Section FailedApproach.

Record Applicative__Dict f := Applicative__Dict_Build {
  liftA2__ : forall {a} {b} {c}, (a -> b -> c) -> f a -> f b -> f c ;
  op_zlztzg____ : forall {a} {b}, f (a -> b) -> f a -> f b ;
  op_ztzg____ : forall {a} {b}, f a -> f b -> f b ;
  pure__ : forall {a}, a -> f a }.

Definition Applicative f `{Functor f} :=
  forall r__, (Applicative__Dict f -> r__) -> r__.
Existing Class Applicative.

Fail Instance Applicative__Foo : Applicative Foo :=
  fun _ k__ =>
    k__ {| liftA2__ := fun {a} {b} {c} => Foo__liftA2 ;
           op_zlztzg____ := fun {a} {b} => Foo__ap ;
           op_ztzg____ := fun {a} {b} => @Foo__ztzg a b;
           pure__ := fun {a} => Foo__pure |}.
(** The term "b" has type "Type@{Applicative__Dict.u0}" while it is
    expected to have type "Type@{Foo__ztzg.u1}" (universe
    inconsistency: Cannot enforce Applicative__Dict.u0 <= Foo__ztzg.u1
    because Foo__ztzg.u1 <= Foo__ap.u0 <= apE.u0 <= FooE.u1 <
    ITree.Core.ITreeDefinition.2 = Applicative__Dict.u0). *)

End FailedApproach.

Print Applicative__Dict.

Reset FailedApproach.

(** The working [Applicative] definition we found. *)
Record Applicative__Dict@{i j p q m} (f : Type@{i} -> Type@{j}) := Applicative__Dict_Build {
  liftA2__ : forall {a : Type@{p}} {b : Type@{q}} {c : Type@{m}}, (a -> b -> c) -> f a -> f b -> f c ;
  op_zlztzg____ : forall {a : Type@{p}} {b : Type@{m}}, f (a -> b) -> f a -> f b ;
  (** To fix it, we need to manually introduce another universe level
      for the second parameter of [op_ztzg____]. *)
  op_ztzg____ : forall {a : Type@{p}} {b : Type@{m}}, f a -> f b -> f b ;
  pure__ : forall {a : Type@{m}}, a -> f a }.

Polymorphic Definition Applicative f `{Functor f} :=
  forall r__, (Applicative__Dict f -> r__) -> r__.
Existing Class Applicative.

Instance Applicative__Foo : Applicative Foo :=
  fun _ k__ =>
    k__ {| liftA2__ := fun {a} {b} {c} => Foo__liftA2 ;
           op_zlztzg____ := fun {a} {b} => Foo__ap ;
           op_ztzg____ := fun {a} {b} => Foo__ztzg;
           pure__ := fun {a} => Foo__pure |}.
