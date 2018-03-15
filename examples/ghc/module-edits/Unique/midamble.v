Program Instance Uniquable__Word : Uniquable GHC.Num.Word :=
  fun _ k => k {| getUnique__ x := MkUnique (Coq.ZArith.BinInt.Z.of_N x) |}.

