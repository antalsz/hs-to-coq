Instance Default__CmmCat  : GHC.Err.Default CmmCat :=
	 { default := GcPtrCat }.
Instance Default__width   : GHC.Err.Default Width :=
	 { default := W80 }.
Instance Default__CmmType : GHC.Err.Default CmmType :=
	 { default := Mk_CmmType GHC.Err.default GHC.Err.default }.
