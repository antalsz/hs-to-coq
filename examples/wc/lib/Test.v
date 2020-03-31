Require Import ITree.ITree.
From ExtLib.Structures Require Functor Applicative.

Require Import GHC.Base.

Set Printing Universes.

Section ApplicativeUniverse.

  Inductive FooE : Type -> Type :=
  | ApE {A B} : itree FooE A -> itree FooE B -> FooE (A * B).

  Definition apE {A B} : itree FooE A -> itree FooE B -> itree FooE (A * B) :=
    embed ApE.
  
  Inductive Foo A :=
  | MkFoo : itree FooE A -> Foo A.

  Arguments MkFoo {_}.

  Definition Foo__fmap {A B} : (A -> B) -> Foo A -> Foo B.
    intros f x. destruct x. constructor.
    apply (Functor.fmap f i).
  Defined.

  Definition Foo__zlzd {A B : Type} : A -> Foo B -> Foo A := Foo__fmap ∘ const.

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

  Definition Foo__ztzg {A B} (x : Foo A) (y : Foo B) : Foo B :=
    Foo__ap (id <$ x) y.

  Fail Instance Applicative__Foo : Applicative Foo :=
  fun _ k__ =>
    k__ {| liftA2__ := fun {a} {b} {c} => Foo__liftA2 ;
           op_zlztzg____ := fun {a} {b} => Foo__ap ;
           op_ztzg____ := fun {a} {b} => @Foo__ztzg a b;
           pure__ := fun {a} => Foo__pure |}.

  Axiom Foo__ztzg_axiom : forall {A B}, Foo A -> Foo B -> Foo B.
  
  Instance Applicative__Foo : Applicative Foo :=
  fun _ k__ =>
    k__ {| liftA2__ := fun {a} {b} {c} => Foo__liftA2 ;
           op_zlztzg____ := fun {a} {b} => Foo__ap ;
           op_ztzg____ := fun {a} {b} => Foo__ztzg_axiom;
           pure__ := fun {a} => Foo__pure |}.
End ApplicativeUniverse.

Fail Require Import SetProofs.
