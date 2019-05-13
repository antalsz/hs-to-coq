Parameter lookupDataCon : Core.DataConId -> Core.DataCon.
Parameter lookupClass   : Core.ClassId -> Core.Class.

(* Make this default so that we can reason about either case. *)
(* Import GHC.Err. *)
(* Definition isStateHackType : unit -> bool := GHC.Err.default. *)

(* The real definition looks like this, but we don't have the type information
   around:
  fun ty =>
    if DynFlags.hasNoStateHack DynFlags.unsafeGlobalDynFlags : bool then false else
    match Type.tyConAppTyCon_maybe ty with
    | Some tycon => tycon GHC.Base.== TysPrim.statePrimTyCon
    | _ => false
    end. *)


