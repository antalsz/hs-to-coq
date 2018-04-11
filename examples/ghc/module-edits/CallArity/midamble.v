Instance Default_CallArityRes : GHC.Err.Default CallArityRes.
Admitted.


Definition arrow_first {b}{c}{d} (f : (b -> c)) : (b * d)%type -> (c * d)%type :=
  fun p => match p with (x,y)=> (f x, y) end.
Definition arrow_second {b}{c}{d} (f : (b -> c)) : (d * b)%type -> (d * c)%type :=
  fun p => match p with (x,y)=> (x, f y) end.

(* ------------------------- mutual recursion hack -------------------- *)

(* ANTALZ: This looks like a good example of structural mutual recursion *) 
Parameter callArityBind
   : VarSet.VarSet ->
     CallArityRes ->
     VarSet.VarSet -> CoreSyn.CoreBind -> (CallArityRes * CoreSyn.CoreBind)%type.
