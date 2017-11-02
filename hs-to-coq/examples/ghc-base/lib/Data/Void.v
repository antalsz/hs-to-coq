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

Inductive Void : Type :=.
(* Converted value declarations: *)

(* Skipping instance instance_GHC_Base_Eq__Void *)

(* Skipping instance instance_GHC_Base_Ord_Void *)

(* Skipping instance instance_GHC_Read_Read_Void *)

(* Skipping instance instance_GHC_Show_Show_Void *)

(* Skipping instance instance_GHC_Arr_Ix_Void *)

(* Skipping instance instance_GHC_Exception_Exception_Void *)

(* Translating `instance GHC.Generics.Generic Void' failed: OOPS! Cannot find
   information for class "GHC.Generics.Generic" unsupported *)

(* Skipping instance instance_Data_Data_Data_Void *)

Definition absurd {a} : Void -> a :=
  fun arg_0__ => match arg_0__ with | a => match a with end end.

Definition vacuous {f} {a} `{GHC.Base.Functor f} : f Void -> f a :=
  GHC.Base.fmap absurd.

(* Unbound variables:
     GHC.Base.Functor GHC.Base.fmap
*)
