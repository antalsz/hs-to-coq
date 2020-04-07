Require Import OrderedTypeEx String.
Import String_as_OT.

Require Import ITree.ITree.
From ExtLib.Structures Require Functor Applicative.

Set Printing Universes.

Record Functor__Dict f := Functor__Dict_Build {
  fmap__ : forall {a} {b}, (a -> b) -> f a -> f b ;
  op_zlzd____ : forall {a} {b}, a -> f b -> f a }.

Definition Functor f :=
  forall r__, (Functor__Dict f -> r__) -> r__.
Existing Class Functor.

Polymorphic Cumulative Record Applicative__Dict@{i j p q m} (f : Type@{i} -> Type@{j}) := Applicative__Dict_Build {
  liftA2__ : forall {a : Type@{p}} {b : Type@{q}} {c : Type@{m}}, (a -> b -> c) -> f a -> f b -> f c ;
  op_zlztzg____ : forall {a : Type@{p}} {b : Type@{m}}, f (a -> b) -> f a -> f b ;
  op_ztzg____ : forall {a : Type@{p}} {b : Type@{m}}, f a -> f b -> f b ;
  pure__ : forall {a : Type@{m}}, a -> f a }.

Polymorphic Definition Applicative f `{Functor f} :=
  forall r__, (Applicative__Dict f -> r__) -> r__.
Existing Class Applicative.

Section ApplicativeUniverse.

  Inductive FooE : Type -> Type :=
  | ApE {A B} : itree FooE A -> itree FooE B -> FooE (A * B).

  Print Universes.

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
  
  Notation "'_GHC.Base.∘_'" := (op_z2218U__).

  Definition Foo__zlzd {A B : Type} : A -> Foo B -> Foo A := op_z2218U__ Foo__fmap const.

  Program Instance Functor__Foo : Functor Foo :=
    fun _ k__ =>
      k__ {| fmap__ := fun {a} {b} => Foo__fmap;
             op_zlzd____ := fun {a} {b} => Foo__zlzd |}.

  Print Universes.

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

  Instance Applicative__Foo : Applicative Foo :=
  fun _ k__ =>
    k__ {| liftA2__ := fun {a} {b} {c} => Foo__liftA2 ;
           op_zlztzg____ := fun {a} {b} => Foo__ap ;
           op_ztzg____ := fun {a} {b} => @Foo__ztzg a b;
           pure__ := fun {a} => Foo__pure |}.

  Axiom Foo__ztzg_axiom : forall {A B}, Foo A -> Foo B -> Foo B.

  (*
  Instance Applicative__Foo : Applicative Foo :=
  fun _ k__ =>
    k__ {| liftA2__ := fun {a} {b} {c} => Foo__liftA2 ;
           op_zlztzg____ := fun {a} {b} => Foo__ap ;
           op_ztzg____ := fun {a} {b} => Foo__ztzg_axiom;
           pure__ := fun {a} => Foo__pure |}.
   *)
End ApplicativeUniverse.

Require Import SetProofs.
