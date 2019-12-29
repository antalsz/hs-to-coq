This contains results about the FGL implementations of [BFS](../graph/graph/Data/Graph/Inductive/Query/BFS.hs) and [Dijkstra's algorithm](../graph/graph/Data/Graph/Inductive/Query/SP.hs).

`Helper.v` contains a few general tactics and lemmas that are used across multiple files.

`NicerQueue.v` provides ways of working with the partial functions in [Queue.hs](../graph/graph/Data/Graph/Inductive/Internal/Queue.hs).

`RealRing.v` provides a typeclass for instance of GHC.Num which are ordered rings, allowing us to use Coq's ring theories and tactics.

`Path.v` contains definitions of paths and shortest paths (weighted and unweighted), as well as (very inefficient) functions to compute shortest weighted and unweighted paths, which are proved correct and used as reference implementations.

`Lex.v` contains a generic well-ordered lexicographic relation, which is used to prove the termination of both BFS and Dijkstra's algorith.

`HeapEquiv.v` and `HeapProofs.v` contains results about the functions in [Heap.hs](../graph/graph/Data/Graph/Inductive/Internal/Heap.hs) (for instance, that the root is always the minimum value in the heap).

`BFSProofs.v` contains the proofs of correctness for the various versions of BFS given.

`WeightedGraphs.v` contains a typeclass for lawful weighted graphs (an extension of the LawfulGraph typeclass).

`SPProofs.v` contains the proofs of correctness for the FGL implementation of Dijkstra's algorithm.
