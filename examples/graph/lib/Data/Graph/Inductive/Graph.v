(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Arrow.
Require Coq.Init.Datatypes.
Require Data.Foldable.
Require Data.Function.
Require Data.IntSet.Internal.
Require Data.Maybe.
Require Data.OldList.
Require Data.Tuple.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Enum.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Tuple.
Import Data.OldList.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Node :=
  GHC.Num.Int%type.

Definition Path :=
  (list Node)%type.

Definition UContext :=
  (list Node * Node * list Node)%type%type.

Definition UDecomp g :=
  (option UContext * g)%type%type.

Definition LNode a :=
  (Node * a)%type%type.

Inductive LPath a : Type := | LP (unLPath : list (LNode a)) : LPath a.

Definition UNode :=
  (LNode unit)%type.

Definition UPath :=
  (list UNode)%type.

Definition LEdge b :=
  (Node * Node * b)%type%type.

Definition UEdge :=
  (LEdge unit)%type.

Inductive GroupEdges b : Type := | GEs : (LEdge (list b)) -> GroupEdges b.

Definition Edge :=
  (Node * Node)%type%type.

Definition Adj b :=
  (list (b * Node)%type)%type.

Definition Context a b :=
  (Adj b * Node * a * Adj b)%type%type.

Definition GDecomp g a b :=
  (Context a b * g a b)%type%type.

Definition MContext a b :=
  (option (Context a b))%type.

Definition Decomp g a b :=
  (MContext a b * g a b)%type%type.

Record Graph__Dict gr := Graph__Dict_Build {
  empty__ : forall {a} {b}, gr a b ;
  isEmpty__ : forall {a} {b}, gr a b -> bool ;
  labEdges__ : forall {a} {b}, gr a b -> list (LEdge b) ;
  labNodes__ : forall {a} {b}, gr a b -> list (LNode a) ;
  matchAny__ : forall {a} {b}, gr a b -> GDecomp gr a b ;
  match___ : forall {a} {b}, Node -> gr a b -> Decomp gr a b ;
  mkGraph__ : forall {a} {b}, list (LNode a) -> list (LEdge b) -> gr a b ;
  noNodes__ : forall {a} {b}, gr a b -> GHC.Num.Int ;
  nodeRange__ : forall {a} {b}, gr a b -> (Node * Node)%type }.

Definition Graph gr :=
  forall r__, (Graph__Dict gr -> r__) -> r__.

Existing Class Graph.

Definition empty `{g__0__ : Graph gr} : forall {a} {b}, gr a b :=
  g__0__ _ (empty__ gr).

Definition isEmpty `{g__0__ : Graph gr} : forall {a} {b}, gr a b -> bool :=
  g__0__ _ (isEmpty__ gr).

Definition labEdges `{g__0__ : Graph gr}
   : forall {a} {b}, gr a b -> list (LEdge b) :=
  g__0__ _ (labEdges__ gr).

Definition labNodes `{g__0__ : Graph gr}
   : forall {a} {b}, gr a b -> list (LNode a) :=
  g__0__ _ (labNodes__ gr).

Definition matchAny `{g__0__ : Graph gr}
   : forall {a} {b}, gr a b -> GDecomp gr a b :=
  g__0__ _ (matchAny__ gr).

Definition match_ `{g__0__ : Graph gr}
   : forall {a} {b}, Node -> gr a b -> Decomp gr a b :=
  g__0__ _ (match___ gr).

Definition mkGraph `{g__0__ : Graph gr}
   : forall {a} {b}, list (LNode a) -> list (LEdge b) -> gr a b :=
  g__0__ _ (mkGraph__ gr).

Definition noNodes `{g__0__ : Graph gr}
   : forall {a} {b}, gr a b -> GHC.Num.Int :=
  g__0__ _ (noNodes__ gr).

Definition nodeRange `{g__0__ : Graph gr}
   : forall {a} {b}, gr a b -> (Node * Node)%type :=
  g__0__ _ (nodeRange__ gr).

Record DynGraph__Dict gr := DynGraph__Dict_Build {
  op_za____ : forall {a} {b}, Context a b -> gr a b -> gr a b }.

Definition DynGraph gr `{(Graph gr)} :=
  forall r__, (DynGraph__Dict gr -> r__) -> r__.

Existing Class DynGraph.

Definition op_za__ `{g__0__ : DynGraph gr}
   : forall {a} {b}, Context a b -> gr a b -> gr a b :=
  g__0__ _ (op_za____ gr).

Notation "'_&_'" := (op_za__).

Infix "&" := (_&_) (at level 99).

Arguments LP {_} _.

Arguments GEs {_} _.

Definition unLPath {a} (arg_0__ : LPath a) :=
  let 'LP unLPath := arg_0__ in
  unLPath.

(* Converted value declarations: *)

Definition ufold {gr} {a} {b} {c} `{(Graph gr)}
   : (Context a b -> c -> c) -> c -> gr a b -> c :=
  GHC.DeferredFix.deferredFix3 (fun ufold
                                (f : (Context a b -> c -> c))
                                (u : c)
                                (g : gr a b) =>
                                  let 'pair c g' := matchAny g in
                                  if isEmpty g : bool then u else
                                  f c (ufold f u g')).

Definition toLEdge {b} : Edge -> b -> LEdge b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair v w, l => pair (pair v w) l
    end.

Definition toEdge {b} : LEdge b -> Edge :=
  fun '(pair (pair v w) _) => pair v w.

Definition slabNodes {gr} {a} {b} `{(Graph gr)} : gr a b -> list (LNode a) :=
  Data.OldList.sortBy (Data.Function.on GHC.Base.compare Data.Tuple.fst)
  GHC.Base.∘
  labNodes.

Definition size {gr} {a} {b} `{(Graph gr)} : gr a b -> GHC.Num.Int :=
  Data.Foldable.length GHC.Base.∘ labEdges.

Definition order {gr} {a} {b} `{(Graph gr)} : gr a b -> GHC.Num.Int :=
  noNodes.

Definition op_ziZC__ {c} {d} {a} {b}
   : (c -> d) -> (a -> b -> c) -> a -> b -> d :=
  _GHC.Base.∘_ GHC.Base.∘ _GHC.Base.∘_.

Notation "'_.:_'" := (op_ziZC__).

Infix ".:" := (_.:_) (at level 99).

Definition nodes {gr} {a} {b} `{(Graph gr)} : gr a b -> list Node :=
  GHC.Base.map Data.Tuple.fst GHC.Base.∘ labNodes.

Definition node' {a} {b} : Context a b -> Node :=
  fun '(pair (pair (pair _ v) _) _) => v.

Definition newNodes {gr} {a} {b} `{(Graph gr)}
   : GHC.Num.Int -> gr a b -> list Node :=
  fun i g =>
    let 'pair _ n := nodeRange g in
    if isEmpty g : bool then GHC.Enum.enumFromTo #0 (i GHC.Num.- #1) else
    GHC.Enum.enumFromTo (n GHC.Num.+ #1) (n GHC.Num.+ i).

Definition neighbors' {a} {b} : Context a b -> list Node :=
  fun '(pair (pair (pair p _) _) s) =>
    Coq.Init.Datatypes.app (GHC.Base.map Data.Tuple.snd p) (GHC.Base.map
                            Data.Tuple.snd s).

Definition mkUGraph {gr} `{(Graph gr)}
   : list Node -> list Edge -> gr unit unit :=
  fun vs es =>
    let labUNodes := GHC.Base.map (GHC.Base.flip GHC.Tuple.pair2 tt) in
    let labUEdges := GHC.Base.map (fun arg_1__ => toLEdge arg_1__ tt) in
    mkGraph (labUNodes vs) (labUEdges es).

Definition mcontext {gr} {a} {b} `{(Graph gr)}
   : gr a b -> Node -> MContext a b :=
  Data.Tuple.fst .: GHC.Base.flip match_.

Definition lneighbors' {a} {b} : Context a b -> Adj b :=
  fun '(pair (pair (pair p _) _) s) => Coq.Init.Datatypes.app p s.

Definition lneighbors {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> Adj b :=
  Data.Maybe.maybe nil lneighbors' .: mcontext.

Definition neighbors {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> list Node :=
  GHC.Base.map Data.Tuple.snd .: lneighbors.

Definition labNode' {a} {b} : Context a b -> LNode a :=
  fun '(pair (pair (pair _ v) l) _) => pair v l.

Definition lab' {a} {b} : Context a b -> a :=
  fun '(pair (pair (pair _ _) l) _) => l.

Definition lab {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> option a :=
  fun g v => (GHC.Base.fmap lab' GHC.Base.∘ Data.Tuple.fst) (match_ v g).

Definition insNode {gr} {a} {b} `{(DynGraph gr)}
   : LNode a -> gr a b -> gr a b :=
  fun '(pair v l) => (fun arg_1__ => pair (pair (pair nil v) l) nil & arg_1__).

Definition insNodes {gr} {a} {b} `{(DynGraph gr)}
   : list (LNode a) -> gr a b -> gr a b :=
  fun vs g => Data.Foldable.foldl' (GHC.Base.flip insNode) g vs.

Definition insEdge {gr} {b} {a} `{(DynGraph gr)}
   : LEdge b -> gr a b -> gr a b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair (pair v w) l, g =>
        let 'pair mcxt g' := match_ v g in
        let 'pair (pair (pair pr _) la) su := Data.Maybe.fromMaybe (GHC.Err.error
                                                                    (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                                                             "insEdge: cannot add edge from non-existent vertex ")
                                                                                            (GHC.Show.show v))) mcxt in
        pair (pair (pair pr v) la) (cons (pair l w) su) & g'
    end.

Definition insEdges {gr} {b} {a} `{(DynGraph gr)}
   : list (LEdge b) -> gr a b -> gr a b :=
  fun es g => Data.Foldable.foldl' (GHC.Base.flip insEdge) g es.

Definition hasNeighborAdj {gr} {b} {a} `{Graph gr} `{GHC.Base.Eq_ b}
   : gr a b -> Node -> (b * Node)%type -> bool :=
  fun gr v a => Data.Foldable.elem a (lneighbors gr v).

Definition hasNeighbor {gr} {a} {b} `{Graph gr}
   : gr a b -> Node -> Node -> bool :=
  fun gr v w => Data.Foldable.elem w (neighbors gr v).

Definition gmap {gr} {a} {b} {c} {d} `{(DynGraph gr)}
   : (Context a b -> Context c d) -> gr a b -> gr c d :=
  fun f => ufold (fun c => (fun arg_0__ => f c & arg_0__)) empty.

Definition nemap {gr} {a} {c} {b} {d} `{(DynGraph gr)}
   : (a -> c) -> (b -> d) -> gr a b -> gr c d :=
  fun fn fe =>
    let fe' := GHC.Base.map (Control.Arrow.first fe) in
    gmap (fun '(pair (pair (pair p v) l) s) =>
            pair (pair (pair (fe' p) v) (fn l)) (fe' s)).

Definition nmap {gr} {a} {c} {b} `{(DynGraph gr)}
   : (a -> c) -> gr a b -> gr c b :=
  fun f =>
    gmap (fun '(pair (pair (pair p v) l) s) => pair (pair (pair p v) (f l)) s).

Definition gfiltermap {gr} {a} {b} {c} {d} `{DynGraph gr}
   : (Context a b -> MContext c d) -> gr a b -> gr c d :=
  fun f => ufold (Data.Maybe.maybe GHC.Base.id _&_ GHC.Base.∘ f) empty.

Definition gelem {gr} {a} {b} `{(Graph gr)} : Node -> gr a b -> bool :=
  fun v => Data.Maybe.isJust GHC.Base.∘ (Data.Tuple.fst GHC.Base.∘ match_ v).

Definition flip2 {a} {b} : (a * b)%type -> (b * a)%type :=
  fun '(pair x y) => pair y x.

Definition eqLists {a} `{(GHC.Base.Eq_ a)} : list a -> list a -> bool :=
  fun xs ys =>
    andb (Data.Foldable.null (xs Data.OldList.\\ ys)) (Data.Foldable.null (ys
                                                                           Data.OldList.\\
                                                                           xs)).

Definition emap {gr} {b} {c} {a} `{(DynGraph gr)}
   : (b -> c) -> gr a b -> gr a c :=
  fun f =>
    let map1 := fun g => GHC.Base.map (Control.Arrow.first g) in
    gmap (fun '(pair (pair (pair p v) l) s) =>
            pair (pair (pair (map1 f p) v) l) (map1 f s)).

Definition edges {gr} {a} {b} `{(Graph gr)} : gr a b -> list Edge :=
  GHC.Base.map toEdge GHC.Base.∘ labEdges.

Definition edgeLabel {b} : LEdge b -> b :=
  fun '(pair (pair _ _) l) => l.

Definition glabEdges {gr} {a} {b} `{(Graph gr)}
   : gr a b -> list (GroupEdges b) :=
  let groupLabels :=
    fun les => toLEdge (toEdge (GHC.Err.head les)) (GHC.Base.map edgeLabel les) in
  GHC.Base.map (GEs GHC.Base.∘ groupLabels) GHC.Base.∘
  (Data.OldList.groupBy (Data.Function.on _GHC.Base.==_ toEdge) GHC.Base.∘
   (Data.OldList.sortBy (Data.Function.on GHC.Base.compare toEdge) GHC.Base.∘
    labEdges)).

Definition equal {a} {b} {gr} `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b} `{Graph gr}
   : gr a b -> gr a b -> bool :=
  fun g g' =>
    andb (slabNodes g GHC.Base.== slabNodes g') (glabEdges g GHC.Base.==
          glabEdges g').

Definition delNodes {gr} {a} {b} `{(Graph gr)}
   : list Node -> gr a b -> gr a b :=
  fun vs g => Data.Foldable.foldl' (Data.Tuple.snd .: GHC.Base.flip match_) g vs.

Definition labnfilter {gr} {a} {b} `{Graph gr}
   : (LNode a -> bool) -> gr a b -> gr a b :=
  fun p gr =>
    delNodes ((GHC.Base.map Data.Tuple.fst GHC.Base.∘
               GHC.List.filter (negb GHC.Base.∘ p)) (labNodes gr)) gr.

Definition labfilter {gr} {a} {b} `{DynGraph gr}
   : (a -> bool) -> gr a b -> gr a b :=
  fun f => labnfilter (f GHC.Base.∘ Data.Tuple.snd).

Definition nfilter {gr} {a} {b} `{DynGraph gr}
   : (Node -> bool) -> gr a b -> gr a b :=
  fun f => labnfilter (f GHC.Base.∘ Data.Tuple.fst).

Definition subgraph {gr} {a} {b} `{DynGraph gr}
   : list Node -> gr a b -> gr a b :=
  fun vs =>
    let vs' := Data.IntSet.Internal.fromList vs in
    nfilter (fun arg_1__ => Data.IntSet.Internal.member arg_1__ vs').

Definition delNode {gr} {a} {b} `{(Graph gr)} : Node -> gr a b -> gr a b :=
  fun v => delNodes (cons v nil).

Definition delLEdgeBy {gr} {b} {a} `{(DynGraph gr)}
   : ((b * Node)%type -> Adj b -> Adj b) -> LEdge b -> gr a b -> gr a b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, pair (pair v w) b, g =>
        match match_ v g with
        | pair None _ => g
        | pair (Some (pair (pair (pair p v') l) s)) g' =>
            pair (pair (pair p v') l) (f (pair b w) s) & g'
        end
    end.

Definition delLEdge {gr} {b} {a} `{DynGraph gr} `{GHC.Base.Eq_ b}
   : LEdge b -> gr a b -> gr a b :=
  delLEdgeBy Data.OldList.delete.

Definition delEdge {gr} {a} {b} `{(DynGraph gr)} : Edge -> gr a b -> gr a b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair v w, g =>
        match match_ v g with
        | pair None _ => g
        | pair (Some (pair (pair (pair p v') l) s)) g' =>
            pair (pair (pair p v') l) (GHC.List.filter ((fun arg_3__ =>
                                                           arg_3__ GHC.Base./= w) GHC.Base.∘
                                                        Data.Tuple.snd) s) &
            g'
        end
    end.

Definition delEdges {gr} {a} {b} `{(DynGraph gr)}
   : list Edge -> gr a b -> gr a b :=
  fun es g => Data.Foldable.foldl' (GHC.Base.flip delEdge) g es.

Definition delAllLEdge {gr} {b} {a} `{DynGraph gr} `{GHC.Base.Eq_ b}
   : LEdge b -> gr a b -> gr a b :=
  delLEdgeBy (GHC.List.filter GHC.Base.∘ _GHC.Base./=_).

Definition deg' {a} {b} : Context a b -> GHC.Num.Int :=
  fun '(pair (pair (pair p _) _) s) =>
    Data.Foldable.length p GHC.Num.+ Data.Foldable.length s.

Definition context4l' {a} {b} : Context a b -> Adj b :=
  fun '(pair (pair (pair p v) _) s) =>
    Coq.Init.Datatypes.app s (GHC.List.filter ((fun arg_1__ =>
                                                  arg_1__ GHC.Base.== v) GHC.Base.∘
                                               Data.Tuple.snd) p).

Definition lsuc' {a} {b} : Context a b -> list (Node * b)%type :=
  GHC.Base.map flip2 GHC.Base.∘ context4l'.

Definition out' {a} {b} : Context a b -> list (LEdge b) :=
  fun '((pair (pair (pair _ v) _) _ as c)) =>
    GHC.Base.map (fun '(pair l w) => pair (pair v w) l) (context4l' c).

Definition outdeg' {a} {b} : Context a b -> GHC.Num.Int :=
  Data.Foldable.length GHC.Base.∘ context4l'.

Definition suc' {a} {b} : Context a b -> list Node :=
  GHC.Base.map Data.Tuple.snd GHC.Base.∘ context4l'.

Definition context4l {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> Adj b :=
  Data.Maybe.maybe nil context4l' .: mcontext.

Definition lsuc {gr} {a} {b} `{(Graph gr)}
   : gr a b -> Node -> list (Node * b)%type :=
  GHC.Base.map flip2 .: context4l.

Definition hasLEdge {gr} {b} {a} `{Graph gr} `{GHC.Base.Eq_ b}
   : gr a b -> LEdge b -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | gr, pair (pair v w) l => Data.Foldable.elem (pair w l) (lsuc gr v)
    end.

Definition out {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> list (LEdge b) :=
  fun g v => GHC.Base.map (fun '(pair l w) => pair (pair v w) l) (context4l g v).

Definition outdeg {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> GHC.Num.Int :=
  Data.Foldable.length .: context4l.

Definition suc {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> list Node :=
  GHC.Base.map Data.Tuple.snd .: context4l.

Definition hasEdge {gr} {a} {b} `{Graph gr} : gr a b -> Edge -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | gr, pair v w => Data.Foldable.elem w (suc gr v)
    end.

Definition context1l' {a} {b} : Context a b -> Adj b :=
  fun '(pair (pair (pair p v) _) s) =>
    Coq.Init.Datatypes.app p (GHC.List.filter ((fun arg_1__ =>
                                                  arg_1__ GHC.Base.== v) GHC.Base.∘
                                               Data.Tuple.snd) s).

Definition indeg' {a} {b} : Context a b -> GHC.Num.Int :=
  Data.Foldable.length GHC.Base.∘ context1l'.

Definition inn' {a} {b} : Context a b -> list (LEdge b) :=
  fun '((pair (pair (pair _ v) _) _ as c)) =>
    GHC.Base.map (fun '(pair l w) => pair (pair w v) l) (context1l' c).

Definition lpre' {a} {b} : Context a b -> list (Node * b)%type :=
  GHC.Base.map flip2 GHC.Base.∘ context1l'.

Definition pre' {a} {b} : Context a b -> list Node :=
  GHC.Base.map Data.Tuple.snd GHC.Base.∘ context1l'.

Definition context1l {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> Adj b :=
  Data.Maybe.maybe nil context1l' .: mcontext.

Definition indeg {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> GHC.Num.Int :=
  Data.Foldable.length .: context1l.

Definition inn {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> list (LEdge b) :=
  fun g v => GHC.Base.map (fun '(pair l w) => pair (pair w v) l) (context1l g v).

Definition lpre {gr} {a} {b} `{(Graph gr)}
   : gr a b -> Node -> list (Node * b)%type :=
  GHC.Base.map flip2 .: context1l.

Definition pre {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> list Node :=
  GHC.Base.map Data.Tuple.snd .: context1l.

Definition context {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> Context a b :=
  fun g v =>
    Data.Maybe.fromMaybe (GHC.Err.error (Coq.Init.Datatypes.app
                                         (GHC.Base.hs_string__ "Match Exception, Node: ") (GHC.Show.show v)))
    (Data.Tuple.fst (match_ v g)).

Definition deg {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> GHC.Num.Int :=
  deg' .: context.

Definition prettify {gr} {a} {b} `{DynGraph gr} `{GHC.Show.Show a}
  `{GHC.Show.Show b}
   : gr a b -> GHC.Base.String :=
  fun g =>
    let showsContext :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair (pair (pair _ n) l) s, sg =>
            GHC.Show.shows n GHC.Base.∘
            ((fun arg_2__ => cons (GHC.Char.hs_char__ ":") arg_2__) GHC.Base.∘
             (GHC.Show.shows l GHC.Base.∘
              (GHC.Show.showString (GHC.Base.hs_string__ "->") GHC.Base.∘
               (GHC.Show.shows s GHC.Base.∘
                ((fun arg_3__ => cons (GHC.Char.hs_char__ "") arg_3__) GHC.Base.∘ sg)))))
        end in
    Data.Foldable.foldr (showsContext GHC.Base.∘ context g) GHC.Base.id (nodes g)
    (GHC.Base.hs_string__ "").

Definition prettyPrint {gr} {a} {b} `{DynGraph gr} `{GHC.Show.Show a}
  `{GHC.Show.Show b}
   : gr a b -> GHC.Types.IO unit :=
  System.IO.putStr GHC.Base.∘ prettify.

Definition buildGr {gr} {a} {b} `{(DynGraph gr)}
   : list (Context a b) -> gr a b :=
  Data.Foldable.foldr _&_ empty.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Graph.Inductive.Graph.Show__GroupEdges' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Graph.Inductive.Graph.Read__GroupEdges' *)

(* Skipping all instances of class `GHC.Read.Read', including
   `Data.Graph.Inductive.Graph.Read__OrdGr' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Graph.Inductive.Graph.Show__OrdGr' *)

Local Definition Ord__LPath_compare {inst_a} `{(GHC.Base.Ord inst_a)}
   : (LPath inst_a) -> (LPath inst_a) -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | LP nil, LP nil => Eq
    | LP (cons (pair _ x) _), LP (cons (pair _ y) _) => GHC.Base.compare x y
    | _, _ =>
        GHC.Err.error (GHC.Base.hs_string__ "LPath: cannot compare two empty paths")
    end.

Local Definition Ord__LPath_op_zl__ {inst_a} `{(GHC.Base.Ord inst_a)}
   : (LPath inst_a) -> (LPath inst_a) -> bool :=
  fun x y => Ord__LPath_compare x y GHC.Base.== Lt.

Local Definition Ord__LPath_op_zlze__ {inst_a} `{(GHC.Base.Ord inst_a)}
   : (LPath inst_a) -> (LPath inst_a) -> bool :=
  fun x y => Ord__LPath_compare x y GHC.Base./= Gt.

Local Definition Ord__LPath_op_zg__ {inst_a} `{(GHC.Base.Ord inst_a)}
   : (LPath inst_a) -> (LPath inst_a) -> bool :=
  fun x y => Ord__LPath_compare x y GHC.Base.== Gt.

Local Definition Ord__LPath_op_zgze__ {inst_a} `{(GHC.Base.Ord inst_a)}
   : (LPath inst_a) -> (LPath inst_a) -> bool :=
  fun x y => Ord__LPath_compare x y GHC.Base./= Lt.

Local Definition Ord__LPath_max {inst_a} `{(GHC.Base.Ord inst_a)}
   : (LPath inst_a) -> (LPath inst_a) -> (LPath inst_a) :=
  fun x y => if Ord__LPath_op_zlze__ x y : bool then y else x.

Local Definition Ord__LPath_min {inst_a} `{(GHC.Base.Ord inst_a)}
   : (LPath inst_a) -> (LPath inst_a) -> (LPath inst_a) :=
  fun x y => if Ord__LPath_op_zlze__ x y : bool then x else y.

Program Instance Ord__LPath {a} `{(GHC.Base.Ord a)} : GHC.Base.Ord (LPath a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__LPath_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__LPath_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__LPath_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__LPath_op_zgze__ ;
           GHC.Base.compare__ := Ord__LPath_compare ;
           GHC.Base.max__ := Ord__LPath_max ;
           GHC.Base.min__ := Ord__LPath_min |}.

Local Definition Eq___LPath_op_zeze__ {inst_a} `{(GHC.Base.Eq_ inst_a)}
   : (LPath inst_a) -> (LPath inst_a) -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | LP nil, LP nil => true
    | LP (cons (pair _ x) _), LP (cons (pair _ y) _) => x GHC.Base.== y
    | LP _, LP _ => false
    end.

Local Definition Eq___LPath_op_zsze__ {inst_a} `{(GHC.Base.Eq_ inst_a)}
   : (LPath inst_a) -> (LPath inst_a) -> bool :=
  fun x y => negb (Eq___LPath_op_zeze__ x y).

Program Instance Eq___LPath {a} `{(GHC.Base.Eq_ a)} : GHC.Base.Eq_ (LPath a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___LPath_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___LPath_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Graph.Inductive.Graph.Show__LPath' *)

Local Definition Eq___GroupEdges_op_zeze__ {inst_b} `{(GHC.Base.Eq_ inst_b)}
   : (GroupEdges inst_b) -> (GroupEdges inst_b) -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | GEs (pair (pair v1 w1) bs1), GEs (pair (pair v2 w2) bs2) =>
        andb (v1 GHC.Base.== v2) (andb (w1 GHC.Base.== w2) (eqLists bs1 bs2))
    end.

Local Definition Eq___GroupEdges_op_zsze__ {inst_b} `{(GHC.Base.Eq_ inst_b)}
   : (GroupEdges inst_b) -> (GroupEdges inst_b) -> bool :=
  fun x y => negb (Eq___GroupEdges_op_zeze__ x y).

Program Instance Eq___GroupEdges {b} `{(GHC.Base.Eq_ b)}
   : GHC.Base.Eq_ (GroupEdges b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___GroupEdges_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___GroupEdges_op_zsze__ |}.

Local Definition Ord__OrdGr_compare {inst_gr} {inst_a} {inst_b} `{Graph inst_gr}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord inst_b}
   : (OrdGr inst_gr inst_a inst_b) ->
     (OrdGr inst_gr inst_a inst_b) -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | OrdGr g1, OrdGr g2 =>
        GHC.Base.mappend ((Data.Function.on GHC.Base.compare (Data.OldList.sort
                                             GHC.Base.∘
                                             labNodes)) g1 g2) ((Data.Function.on GHC.Base.compare (Data.OldList.sort
                                                                                   GHC.Base.∘
                                                                                   labEdges)) g1 g2)
    end.

Local Definition Ord__OrdGr_op_zl__ {inst_gr} {inst_a} {inst_b} `{Graph inst_gr}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord inst_b}
   : (OrdGr inst_gr inst_a inst_b) -> (OrdGr inst_gr inst_a inst_b) -> bool :=
  fun x y => Ord__OrdGr_compare x y GHC.Base.== Lt.

Local Definition Ord__OrdGr_op_zlze__ {inst_gr} {inst_a} {inst_b} `{Graph
  inst_gr} `{GHC.Base.Ord inst_a} `{GHC.Base.Ord inst_b}
   : (OrdGr inst_gr inst_a inst_b) -> (OrdGr inst_gr inst_a inst_b) -> bool :=
  fun x y => Ord__OrdGr_compare x y GHC.Base./= Gt.

Local Definition Ord__OrdGr_op_zg__ {inst_gr} {inst_a} {inst_b} `{Graph inst_gr}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord inst_b}
   : (OrdGr inst_gr inst_a inst_b) -> (OrdGr inst_gr inst_a inst_b) -> bool :=
  fun x y => Ord__OrdGr_compare x y GHC.Base.== Gt.

Local Definition Ord__OrdGr_op_zgze__ {inst_gr} {inst_a} {inst_b} `{Graph
  inst_gr} `{GHC.Base.Ord inst_a} `{GHC.Base.Ord inst_b}
   : (OrdGr inst_gr inst_a inst_b) -> (OrdGr inst_gr inst_a inst_b) -> bool :=
  fun x y => Ord__OrdGr_compare x y GHC.Base./= Lt.

Local Definition Ord__OrdGr_max {inst_gr} {inst_a} {inst_b} `{Graph inst_gr}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord inst_b}
   : (OrdGr inst_gr inst_a inst_b) ->
     (OrdGr inst_gr inst_a inst_b) -> (OrdGr inst_gr inst_a inst_b) :=
  fun x y => if Ord__OrdGr_op_zlze__ x y : bool then y else x.

Local Definition Ord__OrdGr_min {inst_gr} {inst_a} {inst_b} `{Graph inst_gr}
  `{GHC.Base.Ord inst_a} `{GHC.Base.Ord inst_b}
   : (OrdGr inst_gr inst_a inst_b) ->
     (OrdGr inst_gr inst_a inst_b) -> (OrdGr inst_gr inst_a inst_b) :=
  fun x y => if Ord__OrdGr_op_zlze__ x y : bool then x else y.

Program Instance Ord__OrdGr {gr} {a} {b} `{Graph gr} `{GHC.Base.Ord a}
  `{GHC.Base.Ord b}
   : GHC.Base.Ord (OrdGr gr a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__OrdGr_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__OrdGr_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__OrdGr_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__OrdGr_op_zgze__ ;
           GHC.Base.compare__ := Ord__OrdGr_compare ;
           GHC.Base.max__ := Ord__OrdGr_max ;
           GHC.Base.min__ := Ord__OrdGr_min |}.

Local Definition Eq___OrdGr_op_zeze__ {inst_gr} {inst_a} {inst_b} `{Graph
  inst_gr} `{GHC.Base.Ord inst_a} `{GHC.Base.Ord inst_b}
   : (OrdGr inst_gr inst_a inst_b) -> (OrdGr inst_gr inst_a inst_b) -> bool :=
  fun g1 g2 => GHC.Base.compare g1 g2 GHC.Base.== Eq.

Local Definition Eq___OrdGr_op_zsze__ {inst_gr} {inst_a} {inst_b} `{Graph
  inst_gr} `{GHC.Base.Ord inst_a} `{GHC.Base.Ord inst_b}
   : (OrdGr inst_gr inst_a inst_b) -> (OrdGr inst_gr inst_a inst_b) -> bool :=
  fun x y => negb (Eq___OrdGr_op_zeze__ x y).

Program Instance Eq___OrdGr {gr} {a} {b} `{Graph gr} `{GHC.Base.Ord a}
  `{GHC.Base.Ord b}
   : GHC.Base.Eq_ (OrdGr gr a b) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___OrdGr_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___OrdGr_op_zsze__ |}.

Module Notations.
Notation "'_Data.Graph.Inductive.Graph.&_'" := (op_za__).
Infix "Data.Graph.Inductive.Graph.&" := (_&_) (at level 99).
Notation "'_Data.Graph.Inductive.Graph..:_'" := (op_ziZC__).
Infix "Data.Graph.Inductive.Graph..:" := (_.:_) (at level 99).
End Notations.

(* External variables:
     Eq Gt Lt None OrdGr Some andb bool comparison cons false list negb nil op_zt__
     option pair true tt unit Control.Arrow.first Coq.Init.Datatypes.app
     Data.Foldable.elem Data.Foldable.foldl' Data.Foldable.foldr Data.Foldable.length
     Data.Foldable.null Data.Function.on Data.IntSet.Internal.fromList
     Data.IntSet.Internal.member Data.Maybe.fromMaybe Data.Maybe.isJust
     Data.Maybe.maybe Data.OldList.delete Data.OldList.groupBy Data.OldList.op_zrzr__
     Data.OldList.sort Data.OldList.sortBy Data.Tuple.fst Data.Tuple.snd GHC.Base.Eq_
     GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.compare__ GHC.Base.flip
     GHC.Base.fmap GHC.Base.id GHC.Base.map GHC.Base.mappend GHC.Base.max__
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zl____ GHC.Base.op_zlze____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.DeferredFix.deferredFix3
     GHC.Enum.enumFromTo GHC.Err.error GHC.Err.head GHC.List.filter GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Show.Show GHC.Show.show
     GHC.Show.showString GHC.Show.shows GHC.Tuple.pair2 GHC.Types.IO System.IO.putStr
*)
