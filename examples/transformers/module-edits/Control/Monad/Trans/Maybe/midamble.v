Local Definition Monad_tmp {inst_m} `{(GHC.Base.Monad inst_m)}
   : forall {a} {b},
     (MaybeT inst_m) a -> (a -> (MaybeT inst_m) b) -> (MaybeT inst_m) b :=
  fun {a} {b} =>
    fun x f =>
      Mk_MaybeT (runMaybeT x GHC.Base.>>=
                 (fun v =>
                    match v with
                    | None => GHC.Base.return_ None
                    | Some y => runMaybeT (f y)
                    end)).
