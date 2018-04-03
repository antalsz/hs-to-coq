(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require Data.Map.Internal.
Require GHC.Base.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition deleteList {key} {elt} `{GHC.Base.Ord key}
   : list key -> Data.Map.Internal.Map key elt -> Data.Map.Internal.Map key elt :=
  fun ks m => Data.Foldable.foldl (GHC.Base.flip Data.Map.Internal.delete) m ks.

Definition foldRight {elt} {a} {key}
   : (elt -> a -> a) -> a -> Data.Map.Internal.Map key elt -> a :=
  Data.Map.Internal.foldr.

Definition foldRightWithKey {key} {elt} {a}
   : (key -> elt -> a -> a) -> a -> Data.Map.Internal.Map key elt -> a :=
  Data.Map.Internal.foldrWithKey.

Definition insertList {key} {elt} `{GHC.Base.Ord key}
   : list (key * elt)%type ->
     Data.Map.Internal.Map key elt -> Data.Map.Internal.Map key elt :=
  fun xs m =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | m, pair k v => Data.Map.Internal.insert k v m
                           end) m xs.

Definition insertListWith {key} {elt} `{GHC.Base.Ord key}
   : (elt -> elt -> elt) ->
     list (key * elt)%type ->
     Data.Map.Internal.Map key elt -> Data.Map.Internal.Map key elt :=
  fun f xs m0 =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | m, pair k v => Data.Map.Internal.insertWith f k v m
                           end) m0 xs.

(* External variables:
     list op_zt__ pair Data.Foldable.foldl Data.Map.Internal.Map
     Data.Map.Internal.delete Data.Map.Internal.foldr Data.Map.Internal.foldrWithKey
     Data.Map.Internal.insert Data.Map.Internal.insertWith GHC.Base.Ord GHC.Base.flip
*)
