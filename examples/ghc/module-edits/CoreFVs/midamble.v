

(* Break mutual recursion *)
Parameter freeVarsBind1 : Core.CoreBind ->
     DVarSet -> (CoreBindWithFVs * DVarSet)%type.

(*
NOTE (freeVars): if you try to use a termination edit for freeVars instead of 
the rewrite of unzipAndMap in the edit file, we need to add a type
annotation to fv_alt for the freeVars function to type check. 
The required annotation is 
   fv_alt : Alt CoreBndr -> (VarSet.DVarSet * CoreAltWithFVs)
*)
