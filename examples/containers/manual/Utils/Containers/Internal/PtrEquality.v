Parameter ptrEq : forall {a}, a -> a -> bool.
Parameter hetPtrEq : forall {a}{b}, a -> b -> bool.

Axiom ptrEq_eq : forall {a} (x:a)(y:a), ptrEq x y = true -> x = y.