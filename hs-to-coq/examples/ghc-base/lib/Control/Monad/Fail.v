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

Record MonadFail__Dict m `{GHC.Base.Monad m} := {
  fail__ : forall {a}, GHC.Base.String -> m a }.

Definition MonadFail m `{GHC.Base.Monad m} :=
  forall r, (MonadFail__Dict m -> r) -> r.

Existing Class MonadFail.

Definition fail `{g : MonadFail m} : forall {a}, GHC.Base.String -> m a :=
  g _ (fail__ m).
(* Converted value declarations: *)

Local Definition instance_MonadFail_option_fail : forall {a},
                                                    GHC.Base.String -> option a :=
  fun {a} => fun arg_1__ => None.

Instance instance_MonadFail_option : MonadFail option := fun _ k =>
    k {|fail__ := (@instance_MonadFail_option_fail) |}.

Local Definition instance_MonadFail_list_fail : forall {a},
                                                  GHC.Base.String -> list a :=
  fun {a} => fun arg_0__ => nil.

Instance instance_MonadFail_list : MonadFail list := fun _ k =>
    k {|fail__ := (@instance_MonadFail_list_fail) |}.

(* Skipping instance instance_MonadFail_GHC_Types_IO *)

(* Unbound variables:
     GHC.Base.Monad GHC.Base.String None list nil option
*)
