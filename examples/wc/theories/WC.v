Require Import Types.
Require Import Stupid.
Require Import Simple.
Require Import SimpleFold.

Require Import GHC.Base.
Require Import Data.Foldable.
Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Foldable.


Lemma simple_simpleFold : forall file, Types.toTuple (simpleCountFile file) = simpleFoldCountFile file.
Proof.
  induction file.
  + unfold simpleCountFile, simpleFoldCountFile. simpl. 
    admit.
  + unfold simpleCountFile, simpleFoldCountFile. simpl. 
    