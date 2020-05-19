Require Export Freer.
Require Export Proofs.GHC.Base.

Instance FunctorLaws__Freer {E} : FunctorLaws (Freer E).
Admitted.

Instance ApplicativeLaws__Freer {E} : ApplicativeLaws (Freer E).
Admitted.

Instance MonadLaws__Freer {E} : MonadLaws (Freer E).
Admitted.
