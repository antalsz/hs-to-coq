(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted imports: *)

Require GHC.Base.

(* Converted declarations: *)

(* Skipping instance instance_GHC_Base_Eq__Void *)

(* Skipping instance instance_GHC_Base_Ord_Void *)

(* Skipping instance instance_GHC_Read_Read_Void *)

(* Skipping instance instance_GHC_Show_Show_Void *)

(* Skipping instance instance_GHC_Arr_Ix_Void *)

(* Skipping instance instance_GHC_Exception_Exception_Void *)

Inductive Void : Type :=.

Definition absurd {a} : Void -> a :=
  fun arg_0__ => match arg_0__ with | a => match a with end end.

Definition vacuous {f} {a} `{GHC.Base.Functor f} : f Void -> f a :=
  GHC.Base.fmap absurd.

(* Unbound variables:
     GHC.Base.Functor GHC.Base.fmap
*)
