Require Import Data.Graph.Inductive.Graph.
Require Import Lists.List.

Section Weighted.
Context {a : Type} {b : Type} { gr : Type -> Type -> Type} {Hgraph : Graph.Graph gr} {Hlaw : Graph.LawfulGraph gr}
 {Hnum: GHC.Num.Num b} {Heq: Base.Eq_ b} {HOrd: Base.Ord b} {Hreal: @GHC.Real.Real b Hnum Heq HOrd}.

Definition WeIn (g: gr a b) (u v : Node) (w: b) : Prop :=
  In (u,v,w) (labEdges g).


(*More specific properties for weighted graphs*)
Class LawfulWGraph := {
  (*The context for 'match' - NOTE: doesn't play well with multiple edges between nodes, see about this*)  
  Wmatch_context: forall g (v: Node) i x l o g',
    match_ v g = (Some (i, x, l, o), g') -> v = x /\ 
    (forall y w, In (w, y) i <-> WeIn g y v w) /\
    (forall y w, In (w, y) o <-> WeIn g v y w);
  (*The rest of the graph for a match*)
  Wmatch_remain_some: forall g (v: Node) c g',
    match_ v g = (Some c, g') -> 
    (forall u, vIn g' u = true <-> vIn g u = true /\ u <> v) /\
    (forall x y w, WeIn g' x y w <-> WeIn g x y w  /\ x <> v /\ y <> v);
  (*matchAny gives a match_ for some vertex in the graph*)
  WmatchAny_def: forall {a b: Type} (g: gr a b),
    isEmpty g = false ->
    exists v i l o g', matchAny g = ((i, v, l, o), g') /\ vIn g v = true /\
    match_ v g = (Some (i, v, l, o), g')
}.

End Weighted.
