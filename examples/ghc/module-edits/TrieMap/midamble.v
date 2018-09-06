Instance Eq___DeBruijn__unit : GHC.Base.Eq_ (DeBruijn unit) := {}.
Proof.
Admitted.

Instance TrieMap__GenMap
   : forall {m},
     forall `{TrieMap m} `{GHC.Base.Eq_ (Key m)}, TrieMap (GenMap m) :=
  {}.
Proof.
Admitted.

Axiom xtG : forall {m} {a},
            forall `{TrieMap m} `{GHC.Base.Eq_ (Key m)},
            Key m -> XT a -> GenMap m a -> GenMap m a.

Axiom lkG : forall {m} {a},
            forall `{TrieMap m} `{GHC.Base.Eq_ (Key m)}, Key m -> GenMap m a -> option a.
