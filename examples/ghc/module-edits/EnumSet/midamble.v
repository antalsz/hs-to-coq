Require Coq.ZArith.BinInt.
Require GHC.Enum.

Definition toEnumN  {a} `{GHC.Enum.Enum a} n : a := GHC.Enum.toEnum (Coq.ZArith.BinInt.Z.of_N n).
Definition fromEnumN {a} `{GHC.Enum.Enum a} (e : a) := Coq.ZArith.BinInt.Z.to_N (GHC.Enum.fromEnum e).
