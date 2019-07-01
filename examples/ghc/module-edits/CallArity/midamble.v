(* We parameterize this because we don't have type information *)
Axiom typeArity :  Core.Kind -> list BasicTypes.OneShotInfo.

Instance Default_CallArityRes : GHC.Err.Default CallArityRes := 
GHC.Err.Build_Default _ (GHC.Err.default, GHC.Err.default).


(* ------------------------- mutual recursion hack -------------------- *)

(* ANTALZ: This looks like a good example of structural mutual recursion *) 
Parameter callArityBind1
   : Core.VarSet ->
     CallArityRes ->
     Core.VarSet -> Core.CoreBind -> (CallArityRes * Core.CoreBind)%type.
