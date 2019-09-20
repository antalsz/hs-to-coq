(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BinInt.
Require Coq.Init.Datatypes.
Require Data.Graph.Inductive.Graph.
Require Data.Graph.Inductive.Internal.Queue.
Require Data.Graph.Inductive.Internal.RootPath.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Midamble *)

Instance LPath__Default {a} : GHC.Err.Default (Data.Graph.Inductive.Graph.LPath a) :=
  { default := Data.Graph.Inductive.Graph.LP nil }.

Instance Queue__Default {a} : GHC.Err.Default (Data.Graph.Inductive.Internal.Queue.Queue a) :=
  { default := Data.Graph.Inductive.Internal.Queue.MkQueue nil nil }.
(* Converted value declarations: *)

Definition suci {a} {b}
   : Data.Graph.Inductive.Graph.Context a b ->
     GHC.Num.Int -> list (Data.Graph.Inductive.Graph.Node * GHC.Num.Int)%type :=
  fun c i =>
    GHC.List.zip (Data.Graph.Inductive.Graph.suc' c) (GHC.List.replicate
                  (GHC.List.length (Data.Graph.Inductive.Graph.suc' c)) i).

Definition outU {a} {b}
   : Data.Graph.Inductive.Graph.Context a b ->
     list Data.Graph.Inductive.Graph.Edge :=
  fun c =>
    GHC.Base.map Data.Graph.Inductive.Graph.toEdge (Data.Graph.Inductive.Graph.out'
                                                    c).

Program Fixpoint leveln {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
                        (arg_0__ : list (Data.Graph.Inductive.Graph.Node * GHC.Num.Int)%type) (arg_1__
                          : gr a b) {measure (BinInt.Z.abs_nat (Data.Graph.Inductive.Graph.noNodes
                                                                arg_1__))} : list (Data.Graph.Inductive.Graph.Node *
                                                                                   GHC.Num.Int)%type
                   := match arg_0__, arg_1__ with
                      | nil, _ => nil
                      | _, g =>
                          if Bool.Sumbool.sumbool_of_bool (Data.Graph.Inductive.Graph.isEmpty g)
                          then nil else
                          match arg_0__, arg_1__ with
                          | cons (pair v j) vs, g =>
                              match Data.Graph.Inductive.Graph.match_ v g with
                              | pair (Some c) g' =>
                                  cons (pair v j) (leveln (Coq.Init.Datatypes.app vs (suci c (j GHC.Num.+ #1)))
                                        g')
                              | pair None g' => leveln vs g'
                              end
                          | _, _ => GHC.Err.patternFailure
                          end
                      end.
Admit Obligations.

Definition level {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Graph.Node ->
     gr a b -> list (Data.Graph.Inductive.Graph.Node * GHC.Num.Int)%type :=
  fun v => leveln (cons (pair v #0) nil).

Program Fixpoint lbf {gr} {b} {a} `{(Data.Graph.Inductive.Graph.Graph gr)} (q
                       : Data.Graph.Inductive.Internal.Queue.Queue (Data.Graph.Inductive.Graph.LPath
                                                                    b)) (g : gr a b) {measure (BinInt.Z.abs_nat
                      (Data.Graph.Inductive.Graph.noNodes g))}
                   : Data.Graph.Inductive.Internal.RootPath.LRTree b
                   := match Data.Graph.Inductive.Internal.Queue.queueGet q with
                      | pair (Data.Graph.Inductive.Graph.LP (cons (pair v _) _ as p)) q' =>
                          if Bool.Sumbool.sumbool_of_bool (orb
                                                           (Data.Graph.Inductive.Internal.Queue.queueEmpty q)
                                                           (Data.Graph.Inductive.Graph.isEmpty g))
                          then nil else
                          match Data.Graph.Inductive.Graph.match_ v g with
                          | pair (Some c) g' =>
                              cons (Data.Graph.Inductive.Graph.LP p) (lbf
                                    (Data.Graph.Inductive.Internal.Queue.queuePutList (GHC.Base.map (fun v' =>
                                                                                                       Data.Graph.Inductive.Graph.LP
                                                                                                       (cons v' p))
                                                                                       (Data.Graph.Inductive.Graph.lsuc'
                                                                                        c)) q') g')
                          | pair None g' => lbf q' g'
                          end
                      | _ => GHC.Err.patternFailure
                      end.
Admit Obligations.

Definition lbft {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Graph.Node ->
     gr a b -> Data.Graph.Inductive.Internal.RootPath.LRTree b :=
  fun v g =>
    match Data.Graph.Inductive.Graph.out g v with
    | nil => cons (Data.Graph.Inductive.Graph.LP nil) nil
    | cons (pair (pair v' _) l) _ =>
        lbf (Data.Graph.Inductive.Internal.Queue.queuePut (Data.Graph.Inductive.Graph.LP
                                                           (cons (pair v' l) nil))
             Data.Graph.Inductive.Internal.Queue.mkQueue) g
    end.

Definition lesp {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Graph.Node ->
     Data.Graph.Inductive.Graph.Node ->
     gr a b -> Data.Graph.Inductive.Graph.LPath b :=
  fun s t => Data.Graph.Inductive.Internal.RootPath.getLPath t GHC.Base.∘ lbft s.

Definition bfsnInternal {gr} {a} {b} {c} `{(Data.Graph.Inductive.Graph.Graph
   gr)}
   : (Data.Graph.Inductive.Graph.Context a b -> c) ->
     Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Node ->
     gr a b -> list c :=
  fix bfsnInternal (f : (Data.Graph.Inductive.Graph.Context a b -> c)) (q
                     : Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Node) (g
                     : gr a b) : list c
        := let 'pair v q' := Data.Graph.Inductive.Internal.Queue.queueGet q in
           if orb (Data.Graph.Inductive.Internal.Queue.queueEmpty q)
                  (Data.Graph.Inductive.Graph.isEmpty g) : bool
           then nil else
           match Data.Graph.Inductive.Graph.match_ v g with
           | pair (Some c) g' =>
               cons (f c) (bfsnInternal f (Data.Graph.Inductive.Internal.Queue.queuePutList
                                           (Data.Graph.Inductive.Graph.suc' c) q') g')
           | pair None g' => bfsnInternal f q' g'
           end.

Definition bfsnWith {gr} {a} {b} {c} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : (Data.Graph.Inductive.Graph.Context a b -> c) ->
     list Data.Graph.Inductive.Graph.Node -> gr a b -> list c :=
  fun f vs =>
    bfsnInternal f (Data.Graph.Inductive.Internal.Queue.queuePutList vs
                    Data.Graph.Inductive.Internal.Queue.mkQueue).

Definition bfsn {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : list Data.Graph.Inductive.Graph.Node ->
     gr a b -> list Data.Graph.Inductive.Graph.Node :=
  bfsnWith Data.Graph.Inductive.Graph.node'.

Definition bfsWith {gr} {a} {b} {c} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : (Data.Graph.Inductive.Graph.Context a b -> c) ->
     Data.Graph.Inductive.Graph.Node -> gr a b -> list c :=
  fun f v =>
    bfsnInternal f (Data.Graph.Inductive.Internal.Queue.queuePut v
                    Data.Graph.Inductive.Internal.Queue.mkQueue).

Definition bfs {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Graph.Node ->
     gr a b -> list Data.Graph.Inductive.Graph.Node :=
  bfsWith Data.Graph.Inductive.Graph.node'.

Definition bfenInternal {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Edge ->
     gr a b -> list Data.Graph.Inductive.Graph.Edge :=
  fix bfenInternal (q
                     : Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Edge) (g
                     : gr a b) : list Data.Graph.Inductive.Graph.Edge
        := let 'pair (pair u v) q' := Data.Graph.Inductive.Internal.Queue.queueGet q in
           if orb (Data.Graph.Inductive.Internal.Queue.queueEmpty q)
                  (Data.Graph.Inductive.Graph.isEmpty g) : bool
           then nil else
           match Data.Graph.Inductive.Graph.match_ v g with
           | pair (Some c) g' =>
               cons (pair u v) (bfenInternal (Data.Graph.Inductive.Internal.Queue.queuePutList
                                              (outU c) q') g')
           | pair None g' => bfenInternal q' g'
           end.

Definition bfen {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : list Data.Graph.Inductive.Graph.Edge ->
     gr a b -> list Data.Graph.Inductive.Graph.Edge :=
  fun vs =>
    bfenInternal (Data.Graph.Inductive.Internal.Queue.queuePutList vs
                  Data.Graph.Inductive.Internal.Queue.mkQueue).

Definition bfe {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Graph.Node ->
     gr a b -> list Data.Graph.Inductive.Graph.Edge :=
  fun v => bfen (cons (pair v v) nil).

Definition bf {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Path ->
     gr a b -> Data.Graph.Inductive.Internal.RootPath.RTree :=
  fix bf (q
           : Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Path) (g
           : gr a b) : Data.Graph.Inductive.Internal.RootPath.RTree
        := match Data.Graph.Inductive.Internal.Queue.queueGet q with
           | pair (cons v _ as p) q' =>
               if orb (Data.Graph.Inductive.Internal.Queue.queueEmpty q)
                      (Data.Graph.Inductive.Graph.isEmpty g) : bool
               then nil else
               match Data.Graph.Inductive.Graph.match_ v g with
               | pair (Some c) g' =>
                   cons p (bf (Data.Graph.Inductive.Internal.Queue.queuePutList (GHC.Base.map
                                                                                 (fun arg_2__ => cons arg_2__ p)
                                                                                 (Data.Graph.Inductive.Graph.suc' c))
                               q') g')
               | pair None g' => bf q' g'
               end
           | _ => GHC.Err.patternFailure
           end.

Definition bft {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Graph.Node ->
     gr a b -> Data.Graph.Inductive.Internal.RootPath.RTree :=
  fun v =>
    bf (Data.Graph.Inductive.Internal.Queue.queuePut (cons v nil)
        Data.Graph.Inductive.Internal.Queue.mkQueue).

Definition esp {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Graph.Node ->
     Data.Graph.Inductive.Graph.Node -> gr a b -> Data.Graph.Inductive.Graph.Path :=
  fun s t => Data.Graph.Inductive.Internal.RootPath.getPath t GHC.Base.∘ bft s.

(* External variables:
     Bool.Sumbool.sumbool_of_bool None Some bool cons list nil op_zt__ orb pair
     BinInt.Z.abs_nat Coq.Init.Datatypes.app Data.Graph.Inductive.Graph.Context
     Data.Graph.Inductive.Graph.Edge Data.Graph.Inductive.Graph.Graph
     Data.Graph.Inductive.Graph.LP Data.Graph.Inductive.Graph.LPath
     Data.Graph.Inductive.Graph.Node Data.Graph.Inductive.Graph.Path
     Data.Graph.Inductive.Graph.isEmpty Data.Graph.Inductive.Graph.lsuc'
     Data.Graph.Inductive.Graph.match_ Data.Graph.Inductive.Graph.noNodes
     Data.Graph.Inductive.Graph.node' Data.Graph.Inductive.Graph.out
     Data.Graph.Inductive.Graph.out' Data.Graph.Inductive.Graph.suc'
     Data.Graph.Inductive.Graph.toEdge Data.Graph.Inductive.Internal.Queue.Queue
     Data.Graph.Inductive.Internal.Queue.mkQueue
     Data.Graph.Inductive.Internal.Queue.queueEmpty
     Data.Graph.Inductive.Internal.Queue.queueGet
     Data.Graph.Inductive.Internal.Queue.queuePut
     Data.Graph.Inductive.Internal.Queue.queuePutList
     Data.Graph.Inductive.Internal.RootPath.LRTree
     Data.Graph.Inductive.Internal.RootPath.RTree
     Data.Graph.Inductive.Internal.RootPath.getLPath
     Data.Graph.Inductive.Internal.RootPath.getPath GHC.Base.map GHC.Base.op_z2218U__
     GHC.Err.patternFailure GHC.List.length GHC.List.replicate GHC.List.zip
     GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zp__
*)
