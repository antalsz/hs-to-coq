Require Coq.ZArith.BinInt.
Import Coq.ZArith.BinInt.Z.

Require Data.Set.Internal.
Require GHC.Num.
Require Test.QuickCheck.Property.
Require SetProofs.

Instance Arbitrary_Set {a} `{Base.Eq_ a} `{Base.Ord a} : Test.QuickCheck.Property.Arbitrary (Data.Set.Internal.Set_ a) :=
  { arbitrary := Test.QuickCheck.Property.MkGen SetProofs.WF }.

Require GHC.Enum.
Notation enumFromTo := GHC.Enum.enumFromTo.

Coercion is_true : bool >-> Sortclass.
Coercion of_N : Coq.Numbers.BinNums.N >-> Coq.Numbers.BinNums.Z.

Class IsInt (a : Type) `{Integral a} `{Test.QuickCheck.Property.Arbitrary a} :=
  Mk_IsInt { fromIntF {f : Type -> Type} : f Coq.Numbers.BinNums.N -> f a }.
