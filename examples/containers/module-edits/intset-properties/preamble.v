From mathcomp Require Import ssreflect ssrbool.
Set Bullet Behavior "Strict Subproofs".

Require Coq.ZArith.BinInt.
Local Notation Zpow := Coq.ZArith.BinInt.Z.pow.
Local Notation Zle  := Coq.ZArith.BinInt.Z.le.

Require GHC.Enum.
Notation enumFromTo := GHC.Enum.enumFromTo.

Require GHC.Base.
Import GHC.Base.Notations.

Require GHC.Num.

Require IntSetProofs.

Record Gen a := MkGen { unGen : a -> Prop }.
Arguments MkGen {_} _.
Arguments unGen {_} _ _.

Class Arbitrary (a : Type) := { arbitrary : Gen a }.

Class Propable (a : Type) := { toProp : a -> Prop }.


Definition forAll {a prop} `{Propable prop} (g : Gen a) (p : a -> prop) : Prop :=
  forall (x : a), unGen g x -> toProp (p x).


Instance Propable_Prop : Propable Prop :=
  { toProp := id }.

Instance Propable_bool : Propable bool :=
  { toProp := is_true }.

Instance Propable_unit : Propable unit :=
  { toProp := fun _ => True }.

Instance Propable_fn {a prop} `{Arbitrary a} `{Propable prop} : Propable (a -> prop) :=
  { toProp := forAll arbitrary }.


Definition implies {prop} `{Propable prop} (c : bool) (p : prop) : Prop :=
  if c then toProp p else True.
Infix ".==>." := implies (at level 99).

Definition andp {prop1 prop2} `{Propable prop1} `{Propable prop2} (p1 : prop1) (p2 : prop2) : Prop :=
  toProp p1 /\ toProp p2.
Infix ".&&." := andp (at level 99).

Definition orp {prop1 prop2} `{Propable prop1} `{Propable prop2} (p1 : prop1) (p2 : prop2) : Prop :=
  toProp p1 \/ toProp p2.
Infix ".||." := orp (at level 99).


Definition choose {a} `{GHC.Base.Ord a} (range : a * a) : Gen a :=
  MkGen (fun x => (fst range GHC.Base.<= x) && (x GHC.Base.<= snd range)).


Definition skip_classify {prop} `{Propable prop} (_ : bool) (_ : GHC.Base.String) : prop -> Prop :=
  toProp.


Instance Arbitrary_bool : Arbitrary bool :=
  { arbitrary := MkGen xpredT }.

Instance Arbitrary_Int : Arbitrary GHC.Num.Int :=
  { arbitrary := MkGen (fun x => Zle 0 x) }. (* For IntSet *)

Instance Arbitrary_list {a} `{Arbitrary a} : Arbitrary (list a) :=
  { arbitrary := MkGen (Coq.Lists.List.Forall (unGen arbitrary)) }.

Instance Arbitrary_IntSet : Arbitrary Data.IntSet.Internal.IntSet :=
  { arbitrary := MkGen IntSetProofs.WF }.
