(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Graph.
Require Data.Tree.
Require GHC.Base.
Require GHC.Num.
Require GHC.ST.
Require Unique.

(* Converted type declarations: *)

Definition Set_ s :=
  (GHC.Arr.STArray s Data.Graph.Vertex bool)%type.

Inductive Node key payload : Type
  := | DigraphNode (node_payload : payload) (node_key : key) (node_dependencies
    : list key)
   : Node key payload.

Definition ReduceFn key payload :=
  (list (Node key payload) ->
   (Node key payload -> key) ->
   (Data.Graph.Bounds * (Data.Graph.Vertex -> Node key payload) *
    (key -> option Data.Graph.Vertex) *
    list (Data.Graph.Vertex * Node key payload)%type)%type)%type.

Definition WorkItem key payload :=
  (Node key payload * list payload)%type%type.

Definition IntGraph :=
  Data.Graph.Graph%type.

Inductive Graph node : Type
  := | Graph (gr_int_graph : IntGraph) (gr_vertex_to_node
    : Data.Graph.Vertex -> node) (gr_node_to_vertex
    : node -> option Data.Graph.Vertex)
   : Graph node.

Inductive Edge node : Type := | Edge : node -> node -> Edge node.

Arguments DigraphNode {_} {_} _ _ _.

Arguments Graph {_} _ _ _.

Arguments Edge {_} _ _.

Definition node_dependencies {key} {payload} (arg_0__ : Node key payload) :=
  let 'DigraphNode _ _ node_dependencies := arg_0__ in
  node_dependencies.

Definition node_key {key} {payload} (arg_0__ : Node key payload) :=
  let 'DigraphNode _ node_key _ := arg_0__ in
  node_key.

Definition node_payload {key} {payload} (arg_0__ : Node key payload) :=
  let 'DigraphNode node_payload _ _ := arg_0__ in
  node_payload.

Definition gr_int_graph {node} (arg_0__ : Graph node) :=
  let 'Graph gr_int_graph _ _ := arg_0__ in
  gr_int_graph.

Definition gr_node_to_vertex {node} (arg_0__ : Graph node) :=
  let 'Graph _ _ gr_node_to_vertex := arg_0__ in
  gr_node_to_vertex.

Definition gr_vertex_to_node {node} (arg_0__ : Graph node) :=
  let 'Graph _ gr_vertex_to_node _ := arg_0__ in
  gr_vertex_to_node.

(* Converted value declarations: *)

Axiom verticesG : forall {node}, Graph node -> list node.

Axiom vertexReady : forall {s},
                    Set_ s -> IntGraph -> Data.Graph.Vertex -> GHC.ST.ST s bool.

Axiom vertexGroupsS : forall {s},
                      Set_ s ->
                      IntGraph ->
                      list Data.Graph.Vertex -> GHC.ST.ST s (list (list Data.Graph.Vertex)).

Axiom vertexGroupsG : forall {node}, Graph node -> list (list node).

Axiom vertexGroups : IntGraph -> list (list Data.Graph.Vertex).

Axiom transposeG : forall {node}, Graph node -> Graph node.

Axiom topologicalSortG : forall {node}, Graph node -> list node.

Axiom stronglyConnCompG : forall {node},
                          Graph node -> list (Data.Graph.SCC node).

Axiom stronglyConnCompFromEdgedVerticesUniqR : forall {key} {payload},
                                               forall `{Unique.Uniquable key},
                                               list (Node key payload) -> list (Data.Graph.SCC (Node key payload)).

Axiom stronglyConnCompFromEdgedVerticesUniq : forall {key} {payload},
                                              forall `{Unique.Uniquable key},
                                              list (Node key payload) -> list (Data.Graph.SCC payload).

Axiom stronglyConnCompFromEdgedVerticesOrdR : forall {key} {payload},
                                              forall `{GHC.Base.Ord key},
                                              list (Node key payload) -> list (Data.Graph.SCC (Node key payload)).

Axiom stronglyConnCompFromEdgedVerticesOrd : forall {key} {payload},
                                             forall `{GHC.Base.Ord key},
                                             list (Node key payload) -> list (Data.Graph.SCC payload).

Axiom reduceNodesIntoVerticesUniq : forall {key} {payload},
                                    forall `{Unique.Uniquable key}, ReduceFn key payload.

Axiom reduceNodesIntoVerticesOrd : forall {key} {payload},
                                   forall `{GHC.Base.Ord key}, ReduceFn key payload.

Axiom reduceNodesIntoVertices : forall {key} {m} {payload},
                                (list (key * Data.Graph.Vertex)%type -> m) ->
                                (key -> m -> option Data.Graph.Vertex) -> ReduceFn key payload.

Axiom reachablesG : forall {node}, Graph node -> list node -> list node.

Axiom reachableG : forall {node}, Graph node -> node -> list node.

Axiom reachable : IntGraph -> list Data.Graph.Vertex -> list Data.Graph.Vertex.

Axiom preorderF : forall {a}, Data.Tree.Forest a -> list a.

Axiom outdegreeG : forall {node}, Graph node -> node -> option GHC.Num.Int.

Axiom noOutEdges : IntGraph -> list Data.Graph.Vertex.

Axiom mkEmpty : forall {s}, Data.Graph.Bounds -> GHC.ST.ST s (Set_ s).

Axiom indegreeG : forall {node}, Graph node -> node -> option GHC.Num.Int.

Axiom include : forall {s}, Set_ s -> Data.Graph.Vertex -> GHC.ST.ST s unit.

Axiom hasVertexG : forall {node}, Graph node -> node -> bool.

Axiom graphFromEdgedVerticesUniq : forall {key} {payload},
                                   forall `{Unique.Uniquable key},
                                   list (Node key payload) -> Graph (Node key payload).

Axiom graphFromEdgedVerticesOrd : forall {key} {payload},
                                  forall `{GHC.Base.Ord key}, list (Node key payload) -> Graph (Node key payload).

Axiom graphFromEdgedVertices : forall {key} {payload},
                               ReduceFn key payload -> list (Node key payload) -> Graph (Node key payload).

Axiom graphEmpty : Data.Graph.Graph -> bool.

Axiom findCycle : forall {payload} {key},
                  forall `{GHC.Base.Ord key}, list (Node key payload) -> option (list payload).

Axiom emptyGraph : forall {a}, Graph a.

Axiom emptyG : forall {node}, Graph node -> bool.

Axiom edgesG : forall {node}, Graph node -> list (Edge node).

Axiom dfsTopSortG : forall {node}, Graph node -> list (list node).

Axiom degreeG : forall {node},
                (Data.Graph.Graph -> Data.Graph.Table GHC.Num.Int) ->
                Graph node -> node -> option GHC.Num.Int.

Axiom decodeSccs : forall {node},
                   Graph node -> Data.Tree.Forest Data.Graph.Vertex -> list (Data.Graph.SCC node).

Axiom contains : forall {s}, Set_ s -> Data.Graph.Vertex -> GHC.ST.ST s bool.

Axiom componentsG : forall {node}, Graph node -> list (list node).

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Edge' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Node' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Graph' *)

(* External variables:
     bool list op_zt__ option unit Data.Graph.Bounds Data.Graph.Graph Data.Graph.SCC
     Data.Graph.Table Data.Graph.Vertex Data.Tree.Forest GHC.Arr.STArray GHC.Base.Ord
     GHC.Num.Int GHC.ST.ST Unique.Uniquable
*)
