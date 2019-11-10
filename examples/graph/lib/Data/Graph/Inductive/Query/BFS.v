(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinIntDef.

(* Converted imports: *)

Require BinInt.
Require Coq.Init.Datatypes.
Require Data.Graph.Inductive.Graph.
Require Data.Graph.Inductive.Internal.Queue.
Require Data.Graph.Inductive.Internal.RootPath.
Require GHC.Base.
Require GHC.DeferredFix.
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
(* Converted value declarations: *)

Definition suci {a} {b}
   : Data.Graph.Inductive.Graph.Context a b ->
     GHC.Num.Int -> list (Data.Graph.Inductive.Graph.Node * GHC.Num.Int)%type :=
  fun c i =>
    GHC.List.zip (Data.Graph.Inductive.Graph.suc' c) (repeat i (BinInt.Z.to_nat
                                                              (GHC.List.length (Data.Graph.Inductive.Graph.suc' c)))).

Definition outU {a} {b}
   : Data.Graph.Inductive.Graph.Context a b ->
     list Data.Graph.Inductive.Graph.Edge :=
  fun c =>
    GHC.Base.map Data.Graph.Inductive.Graph.toEdge (Data.Graph.Inductive.Graph.out'
                                                    c).

Definition leveln {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : list (Data.Graph.Inductive.Graph.Node * GHC.Num.Int)%type ->
     gr a b -> list (Data.Graph.Inductive.Graph.Node * GHC.Num.Int)%type :=
  GHC.DeferredFix.deferredFix2 (fun leveln
                                (arg_0__ : list (Data.Graph.Inductive.Graph.Node * GHC.Num.Int)%type)
                                (arg_1__ : gr a b) =>
                                  match arg_0__, arg_1__ with
                                  | nil, _ => nil
                                  | _, g =>
                                      if Data.Graph.Inductive.Graph.isEmpty g : bool then nil else
                                      match arg_0__, arg_1__ with
                                      | cons (pair v j) vs, g =>
                                          match Data.Graph.Inductive.Graph.match_ v g with
                                          | pair (Some c) g' =>
                                              cons (pair v j) (leveln (Coq.Init.Datatypes.app vs (suci c (j GHC.Num.+
                                                                                                          #1))) g')
                                          | pair None g' => leveln vs g'
                                          end
                                      | _, _ => GHC.Err.patternFailure
                                      end
                                  end).

Definition level {gr} {a} {b} `{(Data.Graph.Inductive.Graph.Graph gr)}
   : Data.Graph.Inductive.Graph.Node ->
     gr a b -> list (Data.Graph.Inductive.Graph.Node * GHC.Num.Int)%type :=
  fun v => leveln (cons (pair v #0) nil).

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

Definition bfsnInternal {gr} {a} {b} {c} `{(Data.Graph.Inductive.Graph.Graph
   gr)}
   : (Data.Graph.Inductive.Graph.Context a b -> c) ->
     Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Node ->
     gr a b -> list c :=
  GHC.DeferredFix.deferredFix3 (fun bfsnInternal
                                (f : (Data.Graph.Inductive.Graph.Context a b -> c))
                                (q : Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Node)
                                (g : gr a b) =>
                                  let 'pair v q' := Data.Graph.Inductive.Internal.Queue.queueGet q in
                                  if orb (Data.Graph.Inductive.Internal.Queue.queueEmpty q)
                                         (Data.Graph.Inductive.Graph.isEmpty g) : bool
                                  then nil else
                                  match Data.Graph.Inductive.Graph.match_ v g with
                                  | pair (Some c) g' =>
                                      cons (f c) (bfsnInternal f (Data.Graph.Inductive.Internal.Queue.queuePutList
                                                                  (Data.Graph.Inductive.Graph.suc' c) q') g')
                                  | pair None g' => bfsnInternal f q' g'
                                  end).

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
  GHC.DeferredFix.deferredFix2 (fun bfenInternal
                                (q : Data.Graph.Inductive.Internal.Queue.Queue Data.Graph.Inductive.Graph.Edge)
                                (g : gr a b) =>
                                  let 'pair (pair u v) q' := Data.Graph.Inductive.Internal.Queue.queueGet q in
                                  if orb (Data.Graph.Inductive.Internal.Queue.queueEmpty q)
                                         (Data.Graph.Inductive.Graph.isEmpty g) : bool
                                  then nil else
                                  match Data.Graph.Inductive.Graph.match_ v g with
                                  | pair (Some c) g' =>
                                      cons (pair u v) (bfenInternal (Data.Graph.Inductive.Internal.Queue.queuePutList
                                                                     (outU c) q') g')
                                  | pair None g' => bfenInternal q' g'
                                  end).

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

(* External variables:
     None Some bf bool cons lbf list nil op_zt__ orb pair repeat BinInt.Z.to_nat
     Coq.Init.Datatypes.app Data.Graph.Inductive.Graph.Context
     Data.Graph.Inductive.Graph.Edge Data.Graph.Inductive.Graph.Graph
     Data.Graph.Inductive.Graph.LP Data.Graph.Inductive.Graph.LPath
     Data.Graph.Inductive.Graph.Node Data.Graph.Inductive.Graph.Path
     Data.Graph.Inductive.Graph.isEmpty Data.Graph.Inductive.Graph.match_
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
     GHC.DeferredFix.deferredFix2 GHC.DeferredFix.deferredFix3 GHC.Err.patternFailure
     GHC.List.length GHC.List.zip GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zp__
*)
