(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.

(* Converted type declarations: *)

Record MonadFail__Dict (m : Type -> Type) := MonadFail__Dict_Build {
  fail__ : forall {a}, GHC.Base.String -> m a }.

Definition MonadFail (m : Type -> Type) `{GHC.Base.Monad m} :=
  forall r__, (MonadFail__Dict m -> r__) -> r__.
Existing Class MonadFail.

Definition fail `{g__0__ : MonadFail m} : forall {a}, GHC.Base.String -> m a :=
  g__0__ _ (fail__ m).

(* Converted value declarations: *)

Local Definition MonadFail__option_fail
   : forall {a}, GHC.Base.String -> option a :=
  fun {a} => fun arg_0__ => None.

Program Instance MonadFail__option : MonadFail option :=
  fun _ k__ => k__ {| fail__ := fun {a} => MonadFail__option_fail |}.

Local Definition MonadFail__list_fail : forall {a}, GHC.Base.String -> list a :=
  fun {a} => fun arg_0__ => nil.

Program Instance MonadFail__list : MonadFail list :=
  fun _ k__ => k__ {| fail__ := fun {a} => MonadFail__list_fail |}.

(* Skipping instance `Control.Monad.Fail.MonadFail__IO' of class
   `Control.Monad.Fail.MonadFail' *)

(* External variables:
     None Type list nil option GHC.Base.Monad GHC.Base.String
*)
