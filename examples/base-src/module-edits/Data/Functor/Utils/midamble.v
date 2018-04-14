(* We should be able to automatically generate these *)

Instance Unpeel_StateR {s}{a} : Prim.Unpeel (StateR s a) (s -> (s * a)%type)
:= Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_StateR x => x end) Mk_StateR.
Instance Unpeel_StateL {s}{a} : Prim.Unpeel (StateL s a) (s -> (s * a)%type)
:= Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_StateL x => x end) Mk_StateL.
Instance Unpeel_Min {a} : Prim.Unpeel (Min a) (option a)
:= Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_Min x => x end) Mk_Min.
Instance Unpeel_Max {a} : Prim.Unpeel (Max a) (option a)
:= Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_Max x => x end) Mk_Max.
