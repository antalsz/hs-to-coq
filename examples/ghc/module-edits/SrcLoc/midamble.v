(* Default values *)
Require Import GHC.Err.
Instance Default__SrcSpan : Default SrcSpan := Build_Default _ (UnhelpfulSpan default).

Instance Default__RealSrcSpan : Default RealSrcSpan := 
  Build_Default _ (RealSrcSpan' GHC.Err.default GHC.Err.default  GHC.Err.default  
                   GHC.Err.default GHC.Err.default).


Import GHC.Base.ManualNotations.
Definition Ord__RealSrcLoc_op_zl : RealSrcLoc -> RealSrcLoc -> bool :=
  fun a b =>
    let 'ASrcLoc a1 a2 a3 := a in
    let 'ASrcLoc b1 b2 b3 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => true
    | Eq =>
        match (GHC.Base.compare a2 b2) with
        | Lt => true
        | Eq => (a3 GHC.Base.< b3)
        | Gt => false
        end
    | Gt => false
    end.
