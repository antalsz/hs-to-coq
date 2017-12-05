Instance Default_CmmCat  : Panic.Default CmmCat :=
	 { default := GcPtrCat }.
Instance Default_width   : Panic.Default Width :=
	 { default := W80 }.
Instance Default_CmmType : Panic.Default CmmType :=
	 { default := Mk_CmmType Panic.default Panic.default }.
