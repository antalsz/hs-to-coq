Import Notations.

Definition runAccumT {w} {m} {a} : AccumT w m a -> w -> m (a * w)%type :=
  fun arg_0__ => let 'Mk_AccumT f := arg_0__ in f.

Local Definition Monad__AccumT_tmp {inst_w} {inst_m} `{GHC.Base.Monoid
  inst_w} `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (AccumT inst_w inst_m) a ->
     (a -> (AccumT inst_w inst_m) b) -> (AccumT inst_w inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_AccumT (fun w =>
                   let cont_0__ arg_1__ :=
                     let 'pair a w' := arg_1__ in
                     let cont_2__ arg_3__ :=
                       let 'pair b w'' := arg_3__ in
                       GHC.Base.return_ (pair b (GHC.Base.mappend w' w'')) in
                     runAccumT (k a) (GHC.Base.mappend w w') GHC.Base.>>= cont_2__ in
                   runAccumT m w GHC.Base.>>= cont_0__).