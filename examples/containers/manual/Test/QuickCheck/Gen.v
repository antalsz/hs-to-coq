From mathcomp Require Import ssreflect ssrbool.
Set Bullet Behavior "Strict Subproofs".

Require GHC.Base.
Import GHC.Base.Notations.
Require Import Test.QuickCheck.Property.

Definition choose {a} `{GHC.Base.Ord a} (range : a * a) : Gen a :=
  MkGen (fun x => (fst range GHC.Base.<= x) && (x GHC.Base.<= snd range)).

