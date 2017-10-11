Open Scope type_scope.

Inductive ArrowMonad (a : Type -> Type -> Type) b : Type := Mk_ArrowMonad : ((a unit b) -> ArrowMonad a b).

Inductive Kleisli (m : Type -> Type) a b : Type := Mk_Kleisli : (a -> m b) -> Kleisli m a b.
