(* Definition foldl2 {acc} {a} {b} `{GHC.Err.Default acc}
   : (acc -> a -> b -> acc) -> acc -> list a -> list b -> acc :=
  fix foldl2 arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | _, z, nil, nil => z
           | k, z, cons a as_, cons b bs => foldl2 k (k z a b) as_ bs
           | _, _, _, _ => Panic.panic (GHC.Base.hs_string__ "Util: foldl2")
           end. *)



