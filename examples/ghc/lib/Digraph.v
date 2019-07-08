(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require Unique.

(* Converted type declarations: *)

Axiom Set_ : Type -> Type.

Axiom ReduceFn : Type -> Type -> Type.

Inductive Node key payload : Type
  := | DigraphNode (node_payload : payload) (node_key : key) (node_dependencies
    : list key)
   : Node key payload.

Definition WorkItem key payload :=
  (Node key payload * list payload)%type%type.

Axiom IntGraph : Type.

Axiom Graph : Type -> Type.

Inductive Edge node : Type := | Mk_Edge : node -> node -> Edge node.

Arguments DigraphNode {_} {_} _ _ _.

Arguments Mk_Edge {_} _ _.

Definition node_dependencies {key} {payload} (arg_0__ : Node key payload) :=
  let 'DigraphNode _ _ node_dependencies := arg_0__ in
  node_dependencies.

Definition node_key {key} {payload} (arg_0__ : Node key payload) :=
  let 'DigraphNode _ node_key _ := arg_0__ in
  node_key.

Definition node_payload {key} {payload} (arg_0__ : Node key payload) :=
  let 'DigraphNode node_payload _ _ := arg_0__ in
  node_payload.

(* Converted value declarations: *)

Axiom verticesG : forall {node}, Graph node -> list node.

Axiom transposeG : forall {node}, Graph node -> Graph node.

Axiom topologicalSortG : forall {node}, Graph node -> list node.

Axiom reduceNodesIntoVerticesUniq : forall {key} {payload},
                                    forall `{Unique.Uniquable key}, ReduceFn key payload.

Axiom reduceNodesIntoVerticesOrd : forall {key} {payload},
                                   forall `{GHC.Base.Ord key}, ReduceFn key payload.

Axiom reachablesG : forall {node}, Graph node -> list node -> list node.

Axiom reachableG : forall {node}, Graph node -> node -> list node.

Axiom outdegreeG : forall {node}, Graph node -> node -> option nat.

Axiom indegreeG : forall {node}, Graph node -> node -> option nat.

Axiom hasVertexG : forall {node}, Graph node -> node -> bool.

Axiom graphFromEdgedVerticesUniq : forall {key} {payload},
                                   forall `{Unique.Uniquable key},
                                   list (Node key payload) -> Graph (Node key payload).

Axiom graphFromEdgedVerticesOrd : forall {key} {payload},
                                  forall `{GHC.Base.Ord key}, list (Node key payload) -> Graph (Node key payload).

Axiom graphFromEdgedVertices : forall {key} {payload},
                               ReduceFn key payload -> list (Node key payload) -> Graph (Node key payload).

Axiom findCycle : forall {payload} {key},
                  forall `{GHC.Base.Ord key}, list (Node key payload) -> option (list payload).

Axiom emptyGraph : forall {a}, Graph a.

Axiom emptyG : forall {node}, Graph node -> bool.

Axiom edgesG : forall {node}, Graph node -> list (Edge node).

Axiom dfsTopSortG : forall {node}, Graph node -> list (list node).

Axiom componentsG : forall {node}, Graph node -> list (list node).

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Edge' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Node' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Digraph.Outputable__Graph' *)

(* External variables:
     Type bool list nat op_zt__ option GHC.Base.Ord Unique.Uniquable
*)
