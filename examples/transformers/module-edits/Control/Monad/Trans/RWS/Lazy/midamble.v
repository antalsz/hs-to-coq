Local Definition Monad__RWST_tmp {inst_w} {inst_m} {inst_r} {inst_s}
  `{GHC.Base.Monoid inst_w} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (RWST inst_r inst_w inst_s inst_m) a ->
     (a -> (RWST inst_r inst_w inst_s inst_m) b) ->
     (RWST inst_r inst_w inst_s inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_RWST (fun r s =>
                 let cont_0__ arg_1__ :=
                   let 'pair (pair a s') w := arg_1__ in
                   let cont_2__ arg_3__ :=
                     let 'pair (pair b s'') w' := arg_3__ in
                     GHC.Base.return_ (pair (pair b s'') (GHC.Base.mappend w w')) in
                   runRWST (k a) r s' GHC.Base.>>= cont_2__ in
                 runRWST m r s GHC.Base.>>= cont_0__).
