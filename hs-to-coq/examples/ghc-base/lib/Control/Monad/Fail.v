(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.

(* Converted type declarations: *)

Record MonadFail__Dict (m : Type -> Type) := MonadFail__Dict_Build {
  fail__ : forall {a}, GHC.Base.String -> m a }.

Definition MonadFail (m : Type -> Type) `{GHC.Base.Monad m} :=
  forall r, (MonadFail__Dict m -> r) -> r.

Existing Class MonadFail.

Definition fail `{g : MonadFail m} : forall {a}, GHC.Base.String -> m a :=
  g _ (fail__ m).
(* Converted value declarations: *)

(* Translating `instance MonadFail option' failed: OOPS! Cannot find information
   for class "MonadFail" unsupported *)

(* Translating `instance MonadFail list' failed: OOPS! Cannot find information
   for class "MonadFail" unsupported *)

(* Skipping instance instance_MonadFail_GHC_Types_IO *)

(* Unbound variables:
     GHC.Base.Monad GHC.Base.String Type
*)
