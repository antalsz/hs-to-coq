Require GHC.Err.

Definition expectJust {a}`{_:GHC.Err.Default a} :
			GHC.Base.String -> ((option a) -> a) :=
  fun arg_14__ arg_15__ =>
    match arg_14__ , arg_15__ with
      | _ , Some x => x
      | err , None => GHC.Err.error (GHC.Base.hs_string__ "expectJust ")
    end.
