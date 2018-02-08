Require compcert.lib.Integers.
(* Lets import _only_ the Int64 module, otherwise we get an unwanted
   [comparison] into scope. *)
Module Int64 := compcert.lib.Integers.Int64.
