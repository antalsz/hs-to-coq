
Instance Default__Name : GHC.Err.Default Unique
  := GHC.Err.Build_Default _ (MkUnique GHC.Err.default).

Program Instance Uniquable__Word : Uniquable GHC.Num.Word :=
  fun _ k => k {| getUnique__ x := MkUnique x |}.

Parameter mkUnique : GHC.Char.Char -> nat -> Unique.
