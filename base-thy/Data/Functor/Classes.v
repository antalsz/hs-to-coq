Require Import GHC.Base.
Require Import Data.Functor.Classes.

Require Import Proofs.GHC.Base.

Require Import Coq.Logic.FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".


Class Eq1Laws (t:Type -> Type) `{ Data.Functor.Classes.Eq1 t} 
  (f : forall {a:Type} `{Eq_ a}, Eq_ (t a)) :=
  { Eq1_same : forall {a} `{Eq_ a},
      forall x y, Data.Functor.Classes.liftEq op_zeze__ x y = op_zeze__ x y
  }.

