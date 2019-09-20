Instance LPath__Default {a} : GHC.Err.Default (Data.Graph.Inductive.Graph.LPath a) :=
  { default := Data.Graph.Inductive.Graph.LP nil }.

Instance Queue__Default {a} : GHC.Err.Default (Data.Graph.Inductive.Internal.Queue.Queue a) :=
  { default := Data.Graph.Inductive.Internal.Queue.MkQueue nil nil }.