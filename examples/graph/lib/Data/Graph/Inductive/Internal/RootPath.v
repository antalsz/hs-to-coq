(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Graph.Inductive.Graph.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition RTree :=
  (list Data.Graph.Inductive.Graph.Path)%type.

Definition LRTree a :=
  (list (Data.Graph.Inductive.Graph.LPath a))%type.

(* Converted value declarations: *)

Definition first {a} : (list a -> bool) -> list (list a) -> list a :=
  fun p xss => match GHC.List.filter p xss with | nil => nil | cons x _ => x end.

Definition getPath
   : Data.Graph.Inductive.Graph.Node ->
     RTree -> Data.Graph.Inductive.Graph.Path :=
  fun v =>
    GHC.List.reverse GHC.Base.∘
    first (fun arg_0__ =>
             match arg_0__ with
             | cons w _ => w GHC.Base.== v
             | _ => GHC.Err.patternFailure
             end).

Definition findP {a}
   : Data.Graph.Inductive.Graph.Node ->
     LRTree a -> list (Data.Graph.Inductive.Graph.LNode a) :=
  fix findP (arg_0__ : Data.Graph.Inductive.Graph.Node) (arg_1__ : LRTree a)
        : list (Data.Graph.Inductive.Graph.LNode a)
        := match arg_0__, arg_1__ with
           | _, nil => nil
           | v, cons (Data.Graph.Inductive.Graph.LP nil) ps => findP v ps
           | v, cons (Data.Graph.Inductive.Graph.LP (cons (pair w _) _ as p)) ps =>
               if v GHC.Base.== w : bool then p else
               findP v ps
           end.

Definition getDistance {a}
   : Data.Graph.Inductive.Graph.Node -> LRTree a -> option a :=
  fun v t => match findP v t with | nil => None | cons (pair _ d) _ => Some d end.

Definition getLPath {a}
   : Data.Graph.Inductive.Graph.Node ->
     LRTree a -> Data.Graph.Inductive.Graph.LPath a :=
  fun v =>
    Data.Graph.Inductive.Graph.LP GHC.Base.∘ (GHC.List.reverse GHC.Base.∘ findP v).

Definition getLPathNodes {a}
   : Data.Graph.Inductive.Graph.Node ->
     LRTree a -> Data.Graph.Inductive.Graph.Path :=
  fun v =>
    (fun '(Data.Graph.Inductive.Graph.LP p) => GHC.Base.map Data.Tuple.fst p)
    GHC.Base.∘
    getLPath v.

(* External variables:
     None Some bool cons list nil option pair Data.Graph.Inductive.Graph.LNode
     Data.Graph.Inductive.Graph.LP Data.Graph.Inductive.Graph.LPath
     Data.Graph.Inductive.Graph.Node Data.Graph.Inductive.Graph.Path Data.Tuple.fst
     GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Err.patternFailure
     GHC.List.filter GHC.List.reverse
*)
