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
Require Data.Graph.Inductive.Internal.Heap.
Require Data.Graph.Inductive.Internal.RootPath.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Real.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition expand {b} {a} `{(GHC.Real.Real b)}
   : b ->
     Data.Graph.Inductive.Graph.LPath b ->
     Data.Graph.Inductive.Graph.Context a b ->
     list (Data.Graph.Inductive.Internal.Heap.Heap b
           (Data.Graph.Inductive.Graph.LPath b)) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | d, Data.Graph.Inductive.Graph.LP p, pair (pair (pair _ _) _) s =>
        GHC.Base.map (fun '(pair l v) =>
                        Data.Graph.Inductive.Internal.Heap.unit (l GHC.Num.+ d)
                        (Data.Graph.Inductive.Graph.LP (cons (pair v (l GHC.Num.+ d)) p))) s
    end.

Definition dijkstra {gr} {b} {a} `{Data.Graph.Inductive.Graph.Graph gr}
  `{GHC.Real.Real b}
   : Data.Graph.Inductive.Internal.Heap.Heap b (Data.Graph.Inductive.Graph.LPath
                                                b) ->
     gr a b -> Data.Graph.Inductive.Internal.RootPath.LRTree b :=
  fix dijkstra (arg_0__
                 : Data.Graph.Inductive.Internal.Heap.Heap b (Data.Graph.Inductive.Graph.LPath
                                                              b)) (arg_1__ : gr a b)
        : Data.Graph.Inductive.Internal.RootPath.LRTree b
        := match arg_0__, arg_1__ with
           | h, g =>
               if orb (Data.Graph.Inductive.Internal.Heap.isEmpty h)
                      (Data.Graph.Inductive.Graph.isEmpty g) : bool
               then nil else
               match arg_0__, arg_1__ with
               | h, g =>
                   match Data.Graph.Inductive.Internal.Heap.splitMin h with
                   | pair (pair _ (Data.Graph.Inductive.Graph.LP (cons (pair v d) _) as p)) h' =>
                       match Data.Graph.Inductive.Graph.match_ v g with
                       | pair (Some c) g' =>
                           cons p (dijkstra (Data.Graph.Inductive.Internal.Heap.mergeAll (cons h' (expand d
                                                                                                p c))) g')
                       | pair None g' => dijkstra h' g'
                       end
                   | _ => GHC.Err.patternFailure
                   end
               end
           end.

Definition spTree {gr} {b} {a} `{Data.Graph.Inductive.Graph.Graph gr}
  `{GHC.Real.Real b}
   : Data.Graph.Inductive.Graph.Node ->
     gr a b -> Data.Graph.Inductive.Internal.RootPath.LRTree b :=
  fun v =>
    dijkstra (Data.Graph.Inductive.Internal.Heap.unit #0
              (Data.Graph.Inductive.Graph.LP (cons (pair v #0) nil))).

Definition sp {gr} {b} {a} `{Data.Graph.Inductive.Graph.Graph gr}
  `{GHC.Real.Real b}
   : Data.Graph.Inductive.Graph.Node ->
     Data.Graph.Inductive.Graph.Node ->
     gr a b -> option Data.Graph.Inductive.Graph.Path :=
  fun s t g =>
    match Data.Graph.Inductive.Internal.RootPath.getLPathNodes t (spTree s g) with
    | nil => None
    | p => Some p
    end.

Definition spLength {gr} {b} {a} `{Data.Graph.Inductive.Graph.Graph gr}
  `{GHC.Real.Real b}
   : Data.Graph.Inductive.Graph.Node ->
     Data.Graph.Inductive.Graph.Node -> gr a b -> option b :=
  fun s t =>
    Data.Graph.Inductive.Internal.RootPath.getDistance t GHC.Base.∘ spTree s.

(* External variables:
     None Some bool cons list nil option orb pair Data.Graph.Inductive.Graph.Context
     Data.Graph.Inductive.Graph.Graph Data.Graph.Inductive.Graph.LP
     Data.Graph.Inductive.Graph.LPath Data.Graph.Inductive.Graph.Node
     Data.Graph.Inductive.Graph.Path Data.Graph.Inductive.Graph.isEmpty
     Data.Graph.Inductive.Graph.match_ Data.Graph.Inductive.Internal.Heap.Heap
     Data.Graph.Inductive.Internal.Heap.isEmpty
     Data.Graph.Inductive.Internal.Heap.mergeAll
     Data.Graph.Inductive.Internal.Heap.splitMin
     Data.Graph.Inductive.Internal.Heap.unit
     Data.Graph.Inductive.Internal.RootPath.LRTree
     Data.Graph.Inductive.Internal.RootPath.getDistance
     Data.Graph.Inductive.Internal.RootPath.getLPathNodes GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Err.patternFailure GHC.Num.fromInteger GHC.Num.op_zp__
     GHC.Real.Real
*)
