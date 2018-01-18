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
Require Data.Map.Base.
Require GHC.Base.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition deleteList {key} {elt} `{GHC.Base.Ord key} : list
                                                        key -> Data.Map.Base.Map key elt -> Data.Map.Base.Map key elt :=
  fun ks m => Data.Foldable.foldl (GHC.Base.flip Data.Map.Base.delete) m ks.

Definition foldRight {elt} {a} {key} : (elt -> a -> a) -> a -> Data.Map.Base.Map
                                       key elt -> a :=
  Data.Map.Base.foldr.

Definition foldRightWithKey {key} {elt} {a}
    : (key -> elt -> a -> a) -> a -> Data.Map.Base.Map key elt -> a :=
  Data.Map.Base.foldrWithKey.

Definition insertList {key} {elt} `{GHC.Base.Ord key} : list (key *
                                                             elt)%type -> Data.Map.Base.Map key elt -> Data.Map.Base.Map
                                                        key elt :=
  fun xs m =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                          match arg_0__ , arg_1__ with
                            | m , pair k v => Data.Map.Base.insert k v m
                          end) m xs.

Definition insertListWith {key} {elt} `{GHC.Base.Ord key}
    : (elt -> elt -> elt) -> list (key * elt)%type -> Data.Map.Base.Map key
      elt -> Data.Map.Base.Map key elt :=
  fun f xs m0 =>
    Data.Foldable.foldl (fun arg_0__ arg_1__ =>
                          match arg_0__ , arg_1__ with
                            | m , pair k v => Data.Map.Base.insertWith f k v m
                          end) m0 xs.

(* Unbound variables:
     list op_zt__ pair Data.Foldable.foldl Data.Map.Base.Map Data.Map.Base.delete
     Data.Map.Base.foldr Data.Map.Base.foldrWithKey Data.Map.Base.insert
     Data.Map.Base.insertWith GHC.Base.Ord GHC.Base.flip
*)
