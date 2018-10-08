

(* Break mutual recursion *)
Parameter freeVarsBind1 : Core.CoreBind ->
     DVarSet -> (CoreBindWithFVs * DVarSet)%type.

(*
NOTE (freeVars): if you try to use a termination edit for freeVars 
you may need to add a type
annotation to fv_alt for the freeVars function to type check. 
The required annotation is 
   fv_alt : Alt CoreBndr -> (VarSet.DVarSet * CoreAltWithFVs)
*)
