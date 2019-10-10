Program Instance Dijkstra_Default {b} `{Err.Default b} : Err.Default (b * Data.Graph.Inductive.Graph.LPath b *
                                    Data.Graph.Inductive.Internal.Heap.Heap b (Data.Graph.Inductive.Graph.LPath b)).
Next Obligation.
destruct H. apply (default, Data.Graph.Inductive.Graph.LP nil, Data.Graph.Inductive.Internal.Heap.empty).
Defined.