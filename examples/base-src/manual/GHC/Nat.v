(* This module makes standard Haskell type classes available for 
   Coq's nat type *)


Require GHC.Err.
Require GHC.Base.
Require GHC.Num.
Require GHC.Real.
Require GHC.Enum.

Instance Default_nat : GHC.Err.Default nat := 
  GHC.Err.Build_Default _ 0.

Instance Num_nat : GHC.Num.Num nat := {
     op_zp__ := Nat.add;
     op_zm__ := Nat.sub;
     op_zt__ := Nat.mul;
     abs     := fun x => x;
     fromInteger := BinIntDef.Z.to_nat;
     negate  := fun x => x;
     signum  :=  fun x => x; }.

Instance Eq_nat : GHC.Base.Eq_ nat :=
  fun _ k => k {| GHC.Base.op_zeze____ := fun x y => (Nat.eqb x y);
               GHC.Base.op_zsze____ := fun x y => negb (Nat.eqb x y);
            |}.

Instance Ord_nat : GHC.Base.Ord nat :=
  GHC.Base.ord_default Nat.compare.

Instance Real_nat : GHC.Real.Real nat.
Admitted.

Instance Enum_nat : GHC.Enum.Enum nat.
Admitted.