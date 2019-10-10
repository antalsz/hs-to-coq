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
  (*Also see if I need this*)
  match_4: forall (a b : Type) (g : gr a b) v n g' i l o, match_ v g = (Some (i, n, l, o), g') -> v = n;
  mkGraph_def: forall (a b : Type) lv le, Desc (mkGraph lv le) (BinInt.Z.of_nat (@length (LNode a) lv))
     (fun v => In v (@ulabNodes a lv))
     (fun u v => In (u,v) (@ulabEdges b le));
  matchAny_def: forall (a b : Type) (g: gr a b) g' x i l o, isEmpty g = false ->
    matchAny g = ((i, x, l, o), g') ->
    match_ x g = (Some (i, x, l, o), g');
  noNodes_def: forall (a b : Type) (g: gr a b), noNodes g = BinInt.Z.of_nat (length (labNodes g))
  (*TODO: others later, see about translating definitions*)
}.

Lemma match_decr_size: forall {a b : Type} {gr} `{Graph gr} `{LawfulGraph gr} c g' (g: gr a b) v,
  (Some c, g') = match_ v g ->
  BinInt.Z.abs_nat (noNodes g') < BinInt.Z.abs_nat (noNodes g).
Proof.
  intros. symmetry in H2. destruct c. destruct p. destruct p. 
  assert (vIn g v). eapply match_3. apply H2.
  pose proof (noNodes_def _ _ g). assert (length (labNodes g) > 0).
  destruct (length (labNodes g)) eqn : A.
  apply length_zero_iff_nil in A. unfold vIn in H3. unfold ulabNodes_gr in H3. rewrite A in H3.
  destruct H3. omega. destruct (length (labNodes g)) eqn : B. omega.
  assert (v = n) by (eapply match_4; apply H2); subst.
  apply (match_2 a b g n (a2, n, a1, a0) g' n0). assumption. assumption. assumption. intros.
  rewrite !noNodes_def in *.  rewrite Zabs2Nat.id. rewrite Zabs2Nat.id. omega.
Qed.

Lemma matchAny_decr_size: forall {a b : Type} {gr} `{Graph gr} `{LawfulGraph gr} c g' (g: gr a b),
  (c, g') = matchAny g ->
  isEmpty g = false ->
  BinInt.Z.abs_nat (noNodes g') < BinInt.Z.abs_nat (noNodes g).
Proof.
  intros. symmetry in H2. destruct c. destruct p. destruct p. 
  apply (matchAny_def _ _ _ _ _ _ _ _ H3) in H2. symmetry in H2. eapply match_decr_size; apply H2.
Qed.