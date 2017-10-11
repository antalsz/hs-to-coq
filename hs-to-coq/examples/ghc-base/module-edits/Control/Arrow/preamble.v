Open Scope type_scope.

Inductive ArrowMonad (a : Type -> Type -> Type) b : Type := Mk_ArrowMonad : ((a unit b) -> ArrowMonad a b).

Arguments Mk_ArrowMonad {_} {_} _.

Inductive Kleisli (m : Type -> Type) a b : Type := Mk_Kleisli : (a -> m b) -> Kleisli m a b.

Arguments Mk_Kleisli {_} {_} _.
