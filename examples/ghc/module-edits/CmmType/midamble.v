Instance Default_CmmCat  : GHC.Err.Default CmmCat :=
	 { default := GcPtrCat }.
Instance Default_width   : GHC.Err.Default Width :=
	 { default := W80 }.
Instance Default_CmmType : GHC.Err.Default CmmType :=
	 { default := Mk_CmmType GHC.Err.default GHC.Err.default }.
