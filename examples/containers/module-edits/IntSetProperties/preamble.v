Require Data.IntSet.Internal.
Require Test.QuickCheck.Property.
Require IntSetProofs.

Require String.
Import String.StringSyntax.

Instance Arbitrary_IntSet : Test.QuickCheck.Property.Arbitrary Data.IntSet.Internal.IntSet :=
  { arbitrary := Test.QuickCheck.Property.MkGen IntSetProofs.WF }.

Require GHC.Enum.
Notation enumFromTo := GHC.Enum.enumFromTo.

Coercion is_true : bool >-> Sortclass.
