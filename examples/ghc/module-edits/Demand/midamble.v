Instance Unpeel_StrictSig : Prim.Unpeel StrictSig DmdType :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_StrictSig y => y end) Mk_StrictSig.