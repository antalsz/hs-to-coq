(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Omega.
Require Import Lists.List.
(* Converted imports: *)

Require BinInt.
Require Control.Arrow.
Require Coq.Init.Datatypes.
Require Coq.Numbers.BinNums.
Require Data.Foldable.
Require Data.Function.
Require Data.IntSet.Internal.
Require Data.Maybe.
Require Data.OldList.
Require Data.Tuple.
Require Err.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Tuple.
Require String.
Import Data.OldList.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Node :=
  Coq.Numbers.BinNums.N.

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

(* Midamble *)

Definition ulabNodes  {a} l :=
  map (fun (x: Node * a) => let (i, l):= x in i) l.

Definition ulabNodes_gr {gr} `{(Graph gr)} {a} {b} (g: gr a b) :=
  ulabNodes (labNodes g).

Definition ulabEdges {b} l :=
  map (fun (x: Node * Node * b) => match x with |  (u, v, l) => (u,v) end) l.

Definition ulabEdges_gr {gr : Type -> Type -> Type}  {a b : Type} `{(Graph gr)} (g: gr a b) :=
  ulabEdges (labEdges g).

(*We want a specification of a graph*)

(*Find a vertex in a graph*)
Definition vIn {gr a b} `{Graph gr} (g: gr a b) (v: Node) : Prop :=
  In v (ulabNodes_gr g).

(*Find an edge in a graph*)
Definition eIn {gr a b} `{Graph gr} (g: gr a b) (u v: Node) : Prop :=
  In (u,v) (ulabEdges_gr g).

Definition Desc {gr a b} `{Graph gr} (g: gr a b) (sz: GHC.Num.Int) fv fe: Prop :=
  forall (P: (gr a b) -> Prop),
  (forall g',
    noNodes g' =  sz ->
    (forall (v: Node), vIn g' v <-> fv v) -> 
    (forall (u v : Node), eIn g' u v <-> fe u v) ->
  P g') -> P g.


(*Should replace Int with Nat here in noNodes bc it is the length of a list
TODO: see if replacing with a nat is ok or if it should be BinNumsN - we define as length of list,
so should be nat, but ok if have to change - just need things to be aligned*)
Class LawfulGraph (gr: Type  -> Type -> Type) `{Graph gr} := {
  empty_def: forall (a b : Type), Desc (@empty gr _ a b) #0 (fun v => False) (fun u v => False);
  is_empty_def: forall (a b: Type) (g: gr a b), isEmpty g = true <-> Desc g #0 (fun v => False) (fun u v => False);
  (*If the vertex is in the graph, then we can get a context with the vertex we queried, and every predecessor
    is an edge (u', v), while every successor is an edge (v, u') *)
  match_1: forall (a b : Type) (g: gr a b) v, vIn g v -> 
    exists i x l o g', @match_ gr _ a b v g = (Some (i, x, l, o), g') /\ x = v /\ 
    (forall u' l', In (l',u') i -> eIn g u' v) /\ (forall u' l', In (l',u') o -> eIn g v u');
  (*The remaining graph has the same vertices and edges as the previous graph, except for v and its neighbors*)
  match_2: forall (a b : Type) (g: gr a b) v x g' n, vIn g v -> @match_ gr _ a b v g = (Some x, g') ->
    (noNodes g) = BinInt.Z.of_nat (S n) ->
    Desc g' (BinInt.Z.of_nat n) (fun u => vIn g u /\ u <> v) (fun x y => eIn g x y /\ x <> v /\ y <> v);
  (*See if I need this specifically*)
  match_3: forall (a b : Type) (g: gr a b) v x g', match_ v g = (Some x, g') -> vIn g v;
  mkGraph_def: forall (a b : Type) lv le, Desc (mkGraph lv le) (BinInt.Z.of_nat (@length (LNode a) lv))
     (fun v => In v (@ulabNodes a lv))
     (fun u v => In (u,v) (@ulabEdges b le));
  matchAny_def: forall (a b : Type) (g: gr a b) g' x i l o, isEmpty g = false ->
    matchAny g = ((i, x, l, o), g') ->
    match_ x g = (Some (i, x, l, o), g');
  noNodes_def: forall (a b : Type) (g: gr a b), noNodes g = BinInt.Z.of_nat (length (labNodes g))
  (*TODO: others later, see about translating definitions*)
}.

Lemma match_decr_size: forall {a b : Type} {gr} `{Graph gr} `{LawfulGraph gr} c g' (g: gr a b),
  (c, g') = matchAny g ->
  isEmpty g = false ->
  BinInt.Z.abs_nat (noNodes g') < BinInt.Z.abs_nat (noNodes g).
Proof.
  intros. symmetry in H2. destruct c. destruct p. destruct p. 
  apply (matchAny_def _ _ _ _ _ _ _ _ H3) in H2. assert (vIn g n). eapply match_3. apply H2.
  pose proof (noNodes_def _ _ g). assert (length (labNodes g) > 0).
  destruct (length (labNodes g)) eqn : A.
  apply length_zero_iff_nil in A. unfold vIn in H4. unfold ulabNodes_gr in H4. rewrite A in H4.
  destruct H4. omega. destruct (length (labNodes g)) eqn : B. omega.
  apply (match_2 a b g n (a2, n, a1, a0) g' n0). assumption. assumption. assumption. intros.
  rewrite !noNodes_def in *.  rewrite Zabs2Nat.id. rewrite Zabs2Nat.id. omega.
Qed.
(* Converted value declarations: *)

Program Fixpoint ufold {gr} {a} {b} {c} `{Graph gr} `{LawfulGraph gr} (f
                         : Context a b -> c -> c) (u : c) (g : gr a b) {measure (BinInt.Z.abs_nat
                        (noNodes g))} : c
                   := let 'pair c g' := matchAny g in
                      if Bool.Sumbool.sumbool_of_bool (isEmpty g) then u else
                      f c (ufold f u g').
Solve Obligations with ((Tactics.program_simpl; eapply match_decr_size; try (apply Heq_anonymous); auto)).

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
  fun g v =>
    ((@GHC.Base.fmap option _ _ _) lab' GHC.Base.∘ Data.Tuple.fst) (match_ v g).

Definition insNode {gr} {a} {b} `{(DynGraph gr)}
   : LNode a -> gr a b -> gr a b :=
  fun '(pair v l) => (fun arg_1__ => pair (pair (pair nil v) l) nil & arg_1__).

Definition insNodes {gr} {a} {b} `{(DynGraph gr)}
   : list (LNode a) -> gr a b -> gr a b :=
  fun vs g => Data.Foldable.foldl' (GHC.Base.flip insNode) g vs.

Definition insEdge {gr} {b} {a} `{DynGraph gr} `{Err.Default (Context a b)}
   : LEdge b -> gr a b -> gr a b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair (pair v w) l, g =>
        let 'pair mcxt g' := match_ v g in
        let 'pair (pair (pair pr _) la) su := Data.Maybe.fromMaybe (GHC.Err.error
                                                                    (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                                                             "insEdge: cannot add edge from non-existent vertex ")
                                                                                            (GHC.Base.hs_string__
                                                                                             String.EmptyString)))
                                                mcxt in
        pair (pair (pair pr v) la) (cons (pair l w) su) & g'
    end.

Definition insEdges {gr} {b} {a} `{DynGraph gr} `{Err.Default (Context a b)}
   : list (LEdge b) -> gr a b -> gr a b :=
  fun es g => Data.Foldable.foldl' (GHC.Base.flip insEdge) g es.

Definition hasNeighborAdj {gr} {b} {a} `{Graph gr} `{GHC.Base.Eq_ b}
   : gr a b -> Node -> (b * Node)%type -> bool :=
  fun gr v a => GHC.List.elem a (lneighbors gr v).

Definition hasNeighbor {gr} {a} {b} `{Graph gr}
   : gr a b -> Node -> Node -> bool :=
  fun gr v w => Data.Foldable.elem w (neighbors gr v).

Definition gmap {gr} {a} {b} {c} {d} `{DynGraph gr} `{LawfulGraph gr}
   : (Context a b -> Context c d) -> gr a b -> gr c d :=
  fun f => ufold (fun c => (fun arg_0__ => f c & arg_0__)) empty.

Definition nemap {gr} {a} {c} {b} {d} `{DynGraph gr} `{LawfulGraph gr}
   : (a -> c) -> (b -> d) -> gr a b -> gr c d :=
  fun fn fe =>
    let fe' := GHC.Base.map (Control.Arrow.first fe) in
    gmap (fun '(pair (pair (pair p v) l) s) =>
            pair (pair (pair (fe' p) v) (fn l)) (fe' s)).

Definition nmap {gr} {a} {c} {b} `{DynGraph gr} `{LawfulGraph gr}
   : (a -> c) -> gr a b -> gr c b :=
  fun f =>
    gmap (fun '(pair (pair (pair p v) l) s) => pair (pair (pair p v) (f l)) s).

Definition gfiltermap {gr} {a} {b} {c} {d} `{DynGraph gr} `{LawfulGraph gr}
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

Definition emap {gr} {b} {c} {a} `{DynGraph gr} `{LawfulGraph gr}
   : (b -> c) -> gr a b -> gr a c :=
  fun f =>
    let map1 := fun g => GHC.Base.map (Control.Arrow.first g) in
    gmap (fun '(pair (pair (pair p v) l) s) =>
            pair (pair (pair (map1 f p) v) l) (map1 f s)).

Definition edges {gr} {a} {b} `{(Graph gr)} : gr a b -> list Edge :=
  GHC.Base.map toEdge GHC.Base.∘ labEdges.

Definition edgeLabel {b} : LEdge b -> b :=
  fun '(pair (pair _ _) l) => l.

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
    GHC.List.length p GHC.Num.+ GHC.List.length s.

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
  GHC.List.length GHC.Base.∘ context4l'.

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
  GHC.List.length .: context4l.

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
  GHC.List.length GHC.Base.∘ context1l'.

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
  GHC.List.length .: context1l.

Definition inn {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> list (LEdge b) :=
  fun g v => GHC.Base.map (fun '(pair l w) => pair (pair w v) l) (context1l g v).

Definition lpre {gr} {a} {b} `{(Graph gr)}
   : gr a b -> Node -> list (Node * b)%type :=
  GHC.Base.map flip2 .: context1l.

Definition pre {gr} {a} {b} `{(Graph gr)} : gr a b -> Node -> list Node :=
  GHC.Base.map Data.Tuple.snd .: context1l.

Definition context {gr} {a} {b} `{Graph gr} `{Err.Default (Context a b)}
   : gr a b -> Node -> Context a b :=
  fun g v =>
    Data.Maybe.fromMaybe (GHC.Err.error (Coq.Init.Datatypes.app
                                         (GHC.Base.hs_string__ "Match Exception, Node: ") (GHC.Base.hs_string__
                                          String.EmptyString))) (Data.Tuple.fst (match_ v g)).

Definition deg {gr} {a} {b} `{Graph gr} `{Err.Default (Context a b)}
   : gr a b -> Node -> GHC.Num.Int :=
  deg' .: context.

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

(* Skipping all instances of class `GHC.Base.Ord', including
   `Data.Graph.Inductive.Graph.Ord__LPath' *)

(* Skipping all instances of class `GHC.Base.Eq_', including
   `Data.Graph.Inductive.Graph.Eq___LPath' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Data.Graph.Inductive.Graph.Show__LPath' *)

(* Skipping all instances of class `GHC.Base.Eq_', including
   `Data.Graph.Inductive.Graph.Eq___GroupEdges' *)

(* Skipping all instances of class `GHC.Base.Ord', including
   `Data.Graph.Inductive.Graph.Ord__OrdGr' *)

(* Skipping all instances of class `GHC.Base.Eq_', including
   `Data.Graph.Inductive.Graph.Eq___OrdGr' *)

Module Notations.
Notation "'_Data.Graph.Inductive.Graph.&_'" := (op_za__).
Infix "Data.Graph.Inductive.Graph.&" := (_&_) (at level 99).
Notation "'_Data.Graph.Inductive.Graph..:_'" := (op_ziZC__).
Infix "Data.Graph.Inductive.Graph..:" := (_.:_) (at level 99).
End Notations.

(* External variables:
     Bool.Sumbool.sumbool_of_bool LawfulGraph None Some andb bool cons list negb nil
     op_zt__ option pair tt unit BinInt.Z.abs_nat Control.Arrow.first
     Coq.Init.Datatypes.app Coq.Numbers.BinNums.N Data.Foldable.elem
     Data.Foldable.foldl' Data.Foldable.foldr Data.Foldable.length Data.Foldable.null
     Data.Function.on Data.IntSet.Internal.fromList Data.IntSet.Internal.member
     Data.Maybe.fromMaybe Data.Maybe.isJust Data.Maybe.maybe Data.OldList.delete
     Data.OldList.op_zrzr__ Data.OldList.sortBy Data.Tuple.fst Data.Tuple.snd
     Err.Default GHC.Base.Eq_ GHC.Base.compare GHC.Base.flip GHC.Base.fmap
     GHC.Base.hs_string__ GHC.Base.id GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.Err.error GHC.List.elem
     GHC.List.filter GHC.List.length GHC.Num.Int GHC.Num.op_zp__ GHC.Tuple.pair2
     String.EmptyString
*)
