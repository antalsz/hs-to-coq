(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Data.Foldable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require Text.Show.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Heap a b : Type
  := | Empty : Heap a b
  |  Node : a -> b -> list (Heap a b) -> Heap a b.

Arguments Empty {_} {_}.

Arguments Node {_} {_} _ _ _.

(* Converted value declarations: *)

Definition unit {a} {b} : a -> b -> Heap a b :=
  fun key val => Node key val nil.

Definition prettyHeap {a} {b} `{GHC.Show.Show a} `{GHC.Show.Show b}
   : Heap a b -> GHC.Base.String :=
  let fix showsHeap arg_0__
            := match arg_0__ with
               | Empty => GHC.Base.id
               | Node key val nil =>
                   GHC.Show.shows key GHC.Base.∘
                   ((fun arg_1__ => Coq.Init.Datatypes.app (GHC.Base.hs_string__ ": ") arg_1__)
                    GHC.Base.∘
                    GHC.Show.shows val)
               | Node key val hs =>
                   GHC.Show.shows key GHC.Base.∘
                   ((fun arg_3__ => Coq.Init.Datatypes.app (GHC.Base.hs_string__ ": ") arg_3__)
                    GHC.Base.∘
                    (GHC.Show.shows val GHC.Base.∘
                     ((fun arg_4__ => cons (GHC.Char.hs_char__ " ") arg_4__) GHC.Base.∘
                      Text.Show.showListWith showsHeap hs)))
               end in
  (fun arg_7__ => showsHeap arg_7__ (GHC.Base.hs_string__ "")).

Definition printPrettyHeap {a} {b} `{GHC.Show.Show a} `{GHC.Show.Show b}
   : Heap a b -> GHC.Types.IO unit :=
  System.IO.putStrLn GHC.Base.∘ prettyHeap.

Definition merge {a} {b} `{(GHC.Base.Ord a)}
   : Heap a b -> Heap a b -> Heap a b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | h, Empty => h
    | Empty, h => h
    | (Node key1 val1 hs as h), (Node key2 val2 hs' as h') =>
        if key1 GHC.Base.< key2 : bool then Node key1 val1 (cons h' hs) else
        Node key2 val2 (cons h hs')
    end.

Definition mergeAll {a} {b} `{(GHC.Base.Ord a)} : list (Heap a b) -> Heap a b :=
  fix mergeAll (arg_0__ : list (Heap a b)) : Heap a b
        := match arg_0__ with
           | nil => Empty
           | cons h nil => h
           | cons h (cons h' hs) => merge (merge h h') (mergeAll hs)
           end.

Definition splitMin {a} {b} `{(GHC.Base.Ord a)}
   : Heap a b -> (a * b * Heap a b)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Empty => GHC.Err.error (GHC.Base.hs_string__ "Heap.splitMin: empty heap")
    | Node key val hs => pair (pair key val) (mergeAll hs)
    end.

Definition isEmpty {a} {b} : Heap a b -> bool :=
  fun arg_0__ => match arg_0__ with | Empty => true | _ => false end.

Definition insert {a} {b} `{(GHC.Base.Ord a)}
   : (a * b)%type -> Heap a b -> Heap a b :=
  fun '(pair key val) => merge (unit key val).

Definition findMin {a} {b} : Heap a b -> (a * b)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Empty => GHC.Err.error (GHC.Base.hs_string__ "Heap.findMin: empty heap")
    | Node key val _ => pair key val
    end.

Definition empty {a} {b} : Heap a b :=
  Empty.

Definition deleteMin {a} {b} `{(GHC.Base.Ord a)} : Heap a b -> Heap a b :=
  fun arg_0__ =>
    match arg_0__ with
    | Empty => Empty
    | Node _ _ hs => mergeAll hs
    end.

Definition toList {a} {b} `{(GHC.Base.Ord a)} : Heap a b -> list (a * b)%type :=
  fix toList (arg_0__ : Heap a b) : list (a * b)%type
        := match arg_0__ with
           | Empty => nil
           | h => let 'pair x r := pair (findMin h) (deleteMin h) in cons x (toList r)
           end.

Definition build {a} {b} `{(GHC.Base.Ord a)} : list (a * b)%type -> Heap a b :=
  Data.Foldable.foldr insert Empty.

Definition heapsort {a} `{(GHC.Base.Ord a)} : list a -> list a :=
  GHC.Base.map Data.Tuple.fst GHC.Base.∘
  (toList GHC.Base.∘ (build GHC.Base.∘ GHC.Base.map (fun x => pair x x))).

Local Definition Eq___Heap_op_zeze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
  `{GHC.Base.Eq_ inst_b}
   : Heap inst_a inst_b -> Heap inst_a inst_b -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Empty, Empty => true
    | Node a1 a2 a3, Node b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | _, _ => false
    end.

Local Definition Eq___Heap_op_zsze__ {inst_a} {inst_b} `{GHC.Base.Eq_ inst_a}
  `{GHC.Base.Eq_ inst_b}
   : Heap inst_a inst_b -> Heap inst_a inst_b -> bool :=
  fun x y => negb (Eq___Heap_op_zeze__ x y).

Program Instance Eq___Heap {a} {b} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b}
   : GHC.Base.Eq_ (Heap a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Heap_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Heap_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Graph.Inductive.Internal.Heap.Show__Heap' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Graph.Inductive.Internal.Heap.Read__Heap' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `Data.Graph.Inductive.Internal.Heap.NFData__Heap' *)

(* External variables:
     andb bool cons false list negb nil op_zt__ pair true Coq.Init.Datatypes.app
     Data.Foldable.foldr Data.Tuple.fst GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String
     GHC.Base.id GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zl__ GHC.Base.op_zsze____ GHC.Err.error
     GHC.Show.Show GHC.Show.shows GHC.Types.IO System.IO.putStrLn
     Text.Show.showListWith
*)
