Instance LPath__Default {a} : GHC.Err.Default (Data.Graph.Inductive.Graph.LPath a) :=
  { default := Data.Graph.Inductive.Graph.LP nil }.

Instance Queue__Default {a} : GHC.Err.Default (Data.Graph.Inductive.Internal.Queue.Queue a) :=
  { default := Data.Graph.Inductive.Internal.Queue.MkQueue nil nil }.

(*Need to rewrite this because of laziness issue - We cannot call queueGet before knowing that the queue is non-empty*)
Definition bf {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Path ->
     gr a b -> Data.Graph.Inductive.Internal.RootPath.RTree :=
  GHC.DeferredFix.deferredFix2 (fun bf
                                (q : Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Path)
                                (g : gr a b) =>
                                 if orb (Data.Graph.Inductive.Internal.Queue.queueEmpty q)
                                             (Data.Graph.Inductive.Graph.isEmpty g) : bool
                                      then nil else
                                  match Data.Graph.Inductive.Internal.Queue.queueGet q with
                                  | pair (cons v _ as p) q' =>
                                      match Data.Graph.Inductive.Graph.match_ v g with
                                      | pair (Some c) g' =>
                                          cons p (bf (Data.Graph.Inductive.Internal.Queue.queuePutList (GHC.Base.map
                                                                                                        (fun arg_2__ =>
                                                                                                           cons arg_2__
                                                                                                                p)
                                                                                                        (Data.Graph.Inductive.Graph.suc'
                                                                                                         c)) q') g')
                                      | pair None g' => bf q' g'
                                      end
                                  | _ => GHC.Err.patternFailure
                                  end).

Definition lbf {gr} {b} {a} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Internal.Queue.Queue (Data.Graph.Inductive.Graph.LPath
                                                b) ->
     gr a b -> Data.Graph.Inductive.Internal.RootPath.LRTree b :=
  GHC.DeferredFix.deferredFix2 (fun lbf
                                (q
                                  : Data.Graph.Inductive.Internal.Queue.Queue (Data.Graph.Inductive.Graph.LPath
                                                                               b))
                                (g : gr a b) =>
                                 if orb (Data.Graph.Inductive.Internal.Queue.queueEmpty q)
                                             (Data.Graph.Inductive.Graph.isEmpty g) : bool
                                      then nil else
                                  match Data.Graph.Inductive.Internal.Queue.queueGet q with
                                  | pair (Data.Graph.Inductive.Graph.LP (cons (pair v _) _ as p)) q' =>
                                      match Data.Graph.Inductive.Graph.match_ v g with
                                      | pair (Some c) g' =>
                                          cons (Data.Graph.Inductive.Graph.LP p) (lbf
                                                (Data.Graph.Inductive.Internal.Queue.queuePutList (GHC.Base.map
                                                                                                   (fun v' =>
                                                                                                      Data.Graph.Inductive.Graph.LP
                                                                                                      (cons v' p))
                                                                                                   (Data.Graph.Inductive.Graph.lsuc'
                                                                                                    c)) q') g')
                                      | pair None g' => lbf q' g'
                                      end
                                  | _ => GHC.Err.patternFailure
                                  end).