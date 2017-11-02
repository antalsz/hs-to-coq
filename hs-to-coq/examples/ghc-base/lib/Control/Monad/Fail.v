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

Class MonadFail m `{GHC.Base.Monad m} := {
  fail : forall {a}, GHC.Base.String -> m a }.
(* Converted value declarations: *)

Local Definition instance_MonadFail_option_fail : forall {a},
                                                    GHC.Base.String -> option a :=
  fun {a} => fun arg_1__ => None.

Instance instance_MonadFail_option : MonadFail option := {
  fail := fun {a} => instance_MonadFail_option_fail }.

Local Definition instance_MonadFail_list_fail : forall {a},
                                                  GHC.Base.String -> list a :=
  fun {a} => fun arg_0__ => nil.

Instance instance_MonadFail_list : MonadFail list := {
  fail := fun {a} => instance_MonadFail_list_fail }.

(* Skipping instance instance_MonadFail_GHC_Types_IO *)

(* Unbound variables:
     GHC.Base.Monad GHC.Base.String None list nil option
*)
