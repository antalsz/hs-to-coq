Require Import  Test.QuickCheck.Property.

Definition arbitrary : forall {a : Type} `{Arbitrary a}, Gen a
  := @Test.QuickCheck.Property.arbitrary.