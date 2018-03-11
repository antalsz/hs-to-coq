From mathcomp Require Import ssreflect ssrbool.
Set Bullet Behavior "Strict Subproofs".

Require Coq.ZArith.BinInt.
Local Notation Zpow := Coq.ZArith.BinInt.Z.pow.
Local Notation Zle  := Coq.ZArith.BinInt.Z.le.


Require GHC.Base.
Import GHC.Base.Notations.

Require GHC.Num.

Record Gen a := MkGen { unGen : a -> Prop }.
Arguments MkGen {_} _.
Arguments unGen {_} _ _.

Class Arbitrary (a : Type) := { arbitrary : Gen a }.

Class Testable (a : Type) := { toProp : a -> Prop }.


Definition forAll {a prop} `{Testable prop} (g : Gen a) (p : a -> prop) : Prop :=
  forall (x : a), unGen g x -> toProp (p x).
Arguments forAll {_ _ _} / _ _.


Instance Testable_Prop : Testable Prop :=
  { toProp := id }.

Instance Testable_bool : Testable bool :=
  { toProp := is_true }.

Instance Testable_unit : Testable unit :=
  { toProp := fun _ => True }.

Instance Testable_fn {a prop} `{Arbitrary a} `{Testable prop} : Testable (a -> prop) :=
  { toProp := forAll arbitrary }.

Infix ".===." := GHC.Base.op_zeze__ (at level 99).

Definition implies {prop} `{Testable prop} (c : bool) (p : prop) : Prop :=
  if c then toProp p else True.
Infix ".==>." := implies (at level 99).

Definition andp {prop1 prop2} `{Testable prop1} `{Testable prop2} (p1 : prop1) (p2 : prop2) : Prop :=
  toProp p1 /\ toProp p2.
Infix ".&&." := andp (at level 99).

Definition orp {prop1 prop2} `{Testable prop1} `{Testable prop2} (p1 : prop1) (p2 : prop2) : Prop :=
  toProp p1 \/ toProp p2.
Infix ".||." := orp (at level 99).


Definition classify {prop} `{Testable prop} (_ : bool) (_ : GHC.Base.String) : prop -> Prop :=
  toProp.


Instance Arbitrary_bool : Arbitrary bool :=
  { arbitrary := MkGen xpredT }.

Instance Arbitrary_Int : Arbitrary GHC.Num.Int :=
  { arbitrary := MkGen (fun x => Zle 0 x) }. (* For IntSet *)

Instance Arbitrary_list {a} `{Arbitrary a} : Arbitrary (list a) :=
  { arbitrary := MkGen (Coq.Lists.List.Forall (unGen arbitrary)) }.


Module Notations.
Infix "Test.QuickCheck.Property.===" := GHC.Base.op_zeze__ (at level 99).
Infix "Test.QuickCheck.Property.==>" := implies (at level 99).
Infix "Test.QuickCheck.Property..&&." := andp (at level 99).
Infix "Test.QuickCheck.Property..||." := orp (at level 99).
End Notations.
