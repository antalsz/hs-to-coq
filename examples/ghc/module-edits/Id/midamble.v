Parameter lookupDataCon : IdInfo.DataConId -> DataCon.DataCon.
Parameter lookupClass : IdInfo.ClassId -> Class.Class.

(* Make this a parameter so that we can reason about either case. *)
Parameter isStateHackType : unit -> bool.

(* The real definition looks like this, but we don't have the type information
   around:
  fun ty =>
    if DynFlags.hasNoStateHack DynFlags.unsafeGlobalDynFlags : bool then false else
    match Type.tyConAppTyCon_maybe ty with
    | Some tycon => tycon GHC.Base.== TysPrim.statePrimTyCon
    | _ => false
    end. *)


