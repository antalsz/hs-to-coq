Import Notations.

Local Definition Monad__WriterT_tmp {inst_w} {inst_m} `{GHC.Base.Monoid
  inst_w} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (WriterT inst_w inst_m) a ->
     (a -> (WriterT inst_w inst_m) b) -> (WriterT inst_w inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_WriterT (let cont_0__ arg_1__ :=
                    let 'pair a1 w := arg_1__ in
                    let cont_2__ arg_3__ :=
                      let 'pair b1 w' := arg_3__ in
                      GHC.Base.return_ (pair b1 (GHC.Base.mappend w w')) in
                    runWriterT (k a1) GHC.Base.>>= cont_2__ in
                  runWriterT m GHC.Base.>>= cont_0__). 
