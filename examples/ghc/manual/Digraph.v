(* This is all that *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require GHC.Base.

Parameter Graph : Type -> Type.
Definition Node key payload :=
  (payload * key * list key)%type.

Parameter graphFromEdgedVertices : forall {key} {payload} `{GHC.Base.Ord key},
    list (Node key payload) -> Graph (Node key payload).

Parameter topologicalSortG : forall {node}, Graph node -> list node.
