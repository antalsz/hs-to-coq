Require Import List.
Require Import Log.
Require Import Structures.

Require Import GHC.Base.

From ITree Require Import ITree.
From ExtLib.Structures Require Functor Applicative Monad.


Instance Functor'__Output : Functor.Functor Output :=
  {| Functor.fmap := fun A B => @fmap _ Functor__Output A B |}.
 
Instance Applicative'__Output : Applicative.Applicative Output :=
  {| Applicative.pure := fun A => @pure _ _ Applicative__Output A;
     Applicative.ap := fun A B => @op_zlztzg__ _ _ Applicative__Output A B |}.

Instance Monad'__Output : Monad.Monad Output :=
  {| Monad.ret := fun A => @return_ _ _ _ Monad__Output A;
     Monad.bind := fun A B => @op_zgzgze__ _ _ _ Monad__Output A B |}.


Inductive LogMethods : Type -> Type :=
| Out : GHC.Char.Char -> LogMethods unit.

Definition OutputExt : Type -> Type := itree LogMethods.

Definition out' : GHC.Char.Char -> OutputExt unit := embed Out.



Definition handle_logmethods : forall R, LogMethods R -> Output R :=
  fun R e =>
    match e with
    | Out c => MkOutput (fun s => (tt, c :: s))
    end.

Definition interp_output : forall R, OutputExt R ->  R :=
  fun R t => interp handle_logmethods t.
