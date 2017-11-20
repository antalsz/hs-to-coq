Instance Unpeel_Identity c a : Prim.Unpeel (Const a c) a :=
 Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_Const x => x end) Mk_Const.
