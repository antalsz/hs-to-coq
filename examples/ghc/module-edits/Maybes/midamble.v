Require Panic.

Definition expectJust {a}`{_:Panic.Default a} :
			GHC.Base.String -> ((option a) -> a) :=
  fun arg_14__ arg_15__ =>
    match arg_14__ , arg_15__ with
      | _ , Some x => x
      | err , None => Panic.panic (GHC.Base.hs_string__ "expectJust ")
    end.
