Require Import GHC.Base.

Inductive Freer (E : Type -> Type) (R : Type) :=
| Ret (r : R)
| Vis (X : Type) (e : E X) (k : X -> Freer E R).

Arguments Ret {_} {_}.
Arguments Vis {_} {_} {_}.

Set Implicit Arguments.
Set Contextual Implicit.

Section IO.

  Variable E : Type -> Type.
  Variables X Y : Type.

  Fixpoint bind (a : Freer E X) (f : X -> Freer E Y) : Freer E Y :=
    match a with
    | Ret x => f x
    | Vis e k => Vis e (fun x => bind (k x) f)
    end.

  Definition ret (a : X) : Freer E X := Ret a.

  Definition vis (m: E X) : Freer E X := Vis m (fun x => Ret x).

  Definition mask_ (x : Freer E X) : Freer E X := x.
  
  Definition mask (f : (Freer E X -> Freer E X) -> Freer E Y) : Freer E Y :=
    f (fun x => x).

  Definition onException (x : Freer E X) (y : Freer E Y) : Freer E X := x.

  Definition evaluate : X -> Freer E X := ret.

End IO.

Section IOMonad.

  Variable E : Type -> Type.

  Local Definition Functor__IO_fmap
    : forall {a} {b}, (a -> b) -> Freer E a -> Freer E b :=
    fun {a} {b} f x => bind x (fun y => ret (f y)).

  Local Definition Functor__IO_op_zlzd__
    : forall {a} {b}, a -> Freer E b -> Freer E a :=
    fun {a} {b} => Functor__IO_fmap ∘ const.

  Program Instance Functor__IO : Functor (Freer E) :=
    fun _ k =>
      k {| fmap__ := fun {a} {b} => Functor__IO_fmap;
           op_zlzd____ := fun {a} {b} => Functor__IO_op_zlzd__ |}.

  Local Definition Applicative__IO_op_zlztzg__
    : forall {a} {b}, Freer E (a -> b) -> Freer E a -> Freer E b :=
    fun {a} {b} =>
      fun fs xs => bind fs (fun f => bind xs (fun x => ret (f x))).

  Local Definition Applicative__IO_liftA2
    : forall {a} {b} {c}, (a -> b -> c) -> Freer E a -> Freer E b -> Freer E c :=
    fun {a} {b} {c} =>
      fun f xs ys => Applicative__IO_op_zlztzg__ (Functor__IO_fmap f xs) ys.

  Local Definition Applicative__IO_op_ztzg__
    : forall {a} {b}, Freer E a -> Freer E b -> Freer E b :=
    fun {a} {b} =>
      fun xs ys => Applicative__IO_op_zlztzg__ (Functor__IO_op_zlzd__ (fun x => x) xs) ys.

  Local Definition Applicative__IO_pure : forall {a}, a -> Freer E a :=
    fun {a} => @ret E a.

  Program Instance Applicative__IO : Applicative (Freer E) :=
    fun _ k =>
      k {| liftA2__ := fun {a} {b} {c} => Applicative__IO_liftA2 ;
           op_zlztzg____ := fun {a} {b} => Applicative__IO_op_zlztzg__ ;
           op_ztzg____ := fun {a} {b} => Applicative__IO_op_ztzg__ ;
           pure__ := fun {a} => Applicative__IO_pure |}.
  
  Local Definition Monad__IO_return_ : forall {a}, a -> Freer E a :=
    fun {a} => pure.

  Local Definition Monad__IO_op_zgzg__
    : forall {a} {b}, Freer E a -> Freer E b -> Freer E b :=
    fun {a} {b} => _*>_.

  Local Definition Monad__IO_op_zgzgze__
    : forall {a} {b}, Freer E a -> (a -> Freer E b) -> Freer E b :=
    fun {a} {b} => @bind E a b.
  
  Program Instance Monad__IO : Monad (Freer E) :=
    fun _ k =>
      k {| op_zgzg____ := fun {a} {b} => Monad__IO_op_zgzg__ ;
           op_zgzgze____ := fun {a} {b} => Monad__IO_op_zgzgze__ ;
           return___ := fun {a} => Monad__IO_return_ |}.
End IOMonad.
