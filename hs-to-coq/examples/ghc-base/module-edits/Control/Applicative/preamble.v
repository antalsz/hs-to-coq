Inductive WrappedMonad (m : Type -> Type) a : Type := Mk_WrapMonad : m a -> WrappedMonad m a.

Inductive WrappedArrow (a : Type -> Type -> Type) b c : Type := Mk_WrapArrow : a b c -> WrappedArrow a b c.

Arguments Mk_WrapMonad {_} {_} _.

Arguments Mk_WrapArrow {_} {_} {_} _.

Definition unwrapMonad {m} {a} (arg_0__ : WrappedMonad m a) :=
  match arg_0__ with
    | Mk_WrapMonad unwrapMonad => unwrapMonad
  end.

Definition unwrapArrow {a} {b} {c} (arg_1__ : WrappedArrow a b c) :=
  match arg_1__ with
    | Mk_WrapArrow unwrapArrow => unwrapArrow
  end.
