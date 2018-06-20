(* This module makes standard Haskell type classes available for 
   Coq's nat type *)


Require GHC.Err.
Require GHC.Base.
Require GHC.Num.
Require GHC.Real.
Require GHC.Enum.

Instance Default_nat : GHC.Err.Default nat := 
  GHC.Err.Build_Default _ 0.

(* Question: should we replace the - instance with this 
   checked subtraction? *)
Definition error_sub := 
  fun x y => if Nat.ltb x y then GHC.Err.default else Nat.sub x y.

Instance Num_nat : GHC.Num.Num nat := {
     op_zp__ := Nat.add;
     op_zm__ := error_sub;
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


Instance Real_nat : GHC.Real.Real nat :=
  {| Real.toRational := fun x : nat => QArith_base.inject_Z (BinInt.Z.of_nat x) |}.

Definition enumFrom_nat : nat -> list nat := GHC.Err.default.
Definition enumFromTo_nat : nat -> nat -> list nat := 
  fun start stop => List.seq start (error_sub stop start).


Instance Enum_nat : GHC.Enum.Enum nat :=
  {| Enum.enumFrom   := enumFrom_nat;
     Enum.enumFromTo := enumFromTo_nat;
     Enum.pred       := fun x => error_sub x 1;
     Enum.succ       := Nat.succ;
     Enum.toEnum     := BinInt.Z.to_nat;
     Enum.fromEnum   := BinInt.Z.of_nat |}.

