(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted imports: *)

Require GHC.Base.

(* Converted declarations: *)

Local Definition instance_MonadFail_option_fail : forall {a},
                                                    GHC.Base.String -> option a :=
  fun {a} => fun arg_1__ => None.

Local Definition instance_MonadFail_list_fail : forall {a},
                                                  GHC.Base.String -> list a :=
  fun {a} => fun arg_0__ => nil.

(* Skipping instance instance_MonadFail_GHC_Types_IO *)

Class MonadFail m `{GHC.Base.Monad m} := {
  fail : forall {a}, GHC.Base.String -> m a }.

Instance instance_MonadFail_list : !MonadFail list := {
  fail := fun {a} => instance_MonadFail_list_fail }.

Instance instance_MonadFail_option : !MonadFail option := {
  fail := fun {a} => instance_MonadFail_option_fail }.

(* Unbound variables:
     GHC.Base.Monad GHC.Base.String None list nil option
*)
