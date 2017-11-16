Instance Unpeel_Identity a : Prim.Unpeel a (Identity a) :=
 Prim.Build_Unpeel _ _ Mk_Identity (fun arg => match arg with | Mk_Identity x => x end).
Instance Unpeel_CoIdentity a : Prim.Unpeel (Identity a) a :=
 Prim.Build_Unpeel _ _  (fun arg => match arg with | Mk_Identity x => x end) Mk_Identity.
