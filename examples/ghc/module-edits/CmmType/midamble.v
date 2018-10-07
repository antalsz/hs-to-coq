Require Import GHC.Nat.

Instance Default__CmmType : GHC.Err.Default CmmType :=
	 { default := Mk_CmmType GHC.Err.default GHC.Err.default }.
