Definition ulabNodes  {a} l :=
  map (fun (x: Node * a) => let (i, l):= x in i) l.

Definition nodeList {gr} `{(Graph gr)} {a} {b} (g: gr a b) : list Node :=
  ulabNodes (labNodes g).

Definition ulabEdges {b} l :=
  map (fun (x: Node * Node * b) => match x with |  (u, v, l) => (u,v) end) l.

Definition edgeList {gr : Type -> Type -> Type}  {a b : Type} `{(Graph gr)} (g: gr a b) : list Edge :=
  ulabEdges (labEdges g).

Definition mem {A: Type} (x: A) (l: list A)  (H: (forall x y:A, {x = y} + {x <> y}))  : bool :=
  if (in_dec H x l) then true else false.

Definition vIn {gr a b} `{Graph gr} (g: gr a b) (v: Node) : bool :=
  mem v (nodeList g) N.eq_dec.

Lemma pair_dec: forall {a b : Type},
  (forall x y : a, {x = y} + { x <> y}) ->
  (forall x y : b, {x = y} + {x <> y}) ->
  (forall x y : (a * b), {x = y} + { x <> y}).
Proof.
  intros. destruct x. destruct y. specialize (X a0 a1). specialize (X0 b0 b1).
  destruct X. subst. destruct X0. subst. left. reflexivity. right. intro. inversion H; subst; contradiction.
  right. intro. inversion H; subst; contradiction.
Qed.

Definition eIn {gr a b} `{Graph gr} (g: gr a b) (u v : Node) : bool :=
  mem (u,v) (edgeList g) (pair_dec N.eq_dec N.eq_dec).

(*A well formed graph: every function behaves as specified. This may not play too well with graphs with
  multiple edges between nodes.*)
Class LawfulGraph (gr: Type -> Type -> Type) `{Graph gr} := {
  (*Every edge consists of vertices in the graph*)
  edges_valid: forall {a b : Type} (g: gr a b) (u v : Node), eIn g u v = true ->
    vIn g u = true /\ vIn g v = true;
  (*No duplicate vertices (some of the functions have undefined behavior if this is not true)*)
  vertices_valid: forall {a b: Type} (g: gr a b), NoDup (nodeList g);
  (*The empty graph has no vertices*)
  empty_def: forall {a b : Type} (v: Node), vIn (@empty gr _ a b) v = false;
  (*A graph is empty iff it has no vertices*)
  isEmpty_def: forall {a b: Type} (g: gr a b) (v: Node), isEmpty g = true <-> (forall v, vIn g v = false);
  (*Match finds a context iff a vertex is in the graph*)
  match_in: forall {a b : Type} (g: gr a b) (v : Node), (exists c g', match_ v g = (Some c, g')) <-> vIn g v = true;
  (*The context for 'match' - NOTE: doesn't play well with multiple edges between nodes, see about this*)  
  match_context: forall {a b : Type} (g: gr a b) (v: Node) i x l o g',
    match_ v g = (Some (i, x, l, o), g') -> v = x /\ 
    (forall y, In y (map snd i) <-> eIn g y v = true) /\
    (forall y, In y (map snd o) <-> eIn g v y = true);
  (*The rest of the graph for a match*)
  match_remain_some: forall {a b: Type} (g: gr a b) (v: Node) c g',
    match_ v g = (Some c, g') -> 
    (forall u, vIn g' u = true <-> vIn g u = true /\ u <> v) /\
    (forall x y, eIn g' x y = true <-> eIn g x y = true /\ x <> v /\ y <> v);
  (*This is true in the STArray and IOArray implementations, and makes things much simpler*)
  match_remain_none: forall {a b: Type} (g: gr a b) (v: Node) g',
    match_ v g = (None, g') ->
    g = g';
  (*matchAny gives a match_ for some vertex in the graph*)
  matchAny_def: forall {a b: Type} (g: gr a b),
    isEmpty g = false ->
    exists v i l o g', matchAny g = ((i, v, l, o), g') /\ vIn g v = true /\
    match_ v g = (Some (i, v, l, o), g');
  (*noNodes is number of nodes in list (another reason why no duplicates is important)*)
  noNodes_def: forall {a b: Type} (g: gr a b),
    Z.abs_nat (noNodes g) = length (labNodes g)
}.

(*It turns out to be very annoying to prove that match_ decreases the size of the graph. The easiest way
  found is to prove that the new vertex list along with the vertex is a permutation of the original list,
  and so has the same length. We need to prove an auxiliary lemma first.*)
Lemma perm_remove: forall {A: Type} (l l': list A)(x : A),
  (forall (x y : A), {x = y} + { x <> y}) ->
  In x l' ->
  (forall y, In y l <-> In y l' /\ y <> x) ->
  NoDup l ->
  NoDup l' ->
  Permutation l' (x :: l).
Proof.
  intros. assert (forall y, In y l' <-> In y (x :: l)). { simpl. split; intros.
  destruct (X x y). left. assumption. right. rewrite H0. split. assumption. auto.
  destruct H3. subst. assumption. apply H0 in H3. intuition. }
  assert (~In x l). intro. rewrite H0 in H4. destruct H4. contradiction.
  assert (NoDup (x :: l)). constructor. assumption. assumption.
  apply NoDup_Permutation. assumption. assumption. apply H3.
Qed.

Lemma match_decr_size: forall {a b : Type} {gr} `{Graph gr} `{LawfulGraph gr} c g' (g: gr a b) v,
  (Some c, g') = match_ v g ->
  BinInt.Z.abs_nat (noNodes g') < BinInt.Z.abs_nat (noNodes g).
Proof.
  intros. rewrite noNodes_def. rewrite noNodes_def. 
  pose proof (vertices_valid g'). 
  assert (length (labNodes g') = length(nodeList g')). unfold nodeList. unfold ulabNodes.
  rewrite map_length. reflexivity. rewrite H4. clear H4. assert (length (labNodes g) = length (nodeList g)).
  unfold nodeList. unfold ulabNodes. rewrite map_length. reflexivity. rewrite H4. clear H4.
   symmetry in H2.
  pose proof (match_remain_some g v c g' H2). destruct H4. clear H5.
  assert (forall u, In u (nodeList g') <-> In u (nodeList g) /\ u <> v). { intros.
  specialize (H4 u). unfold vIn in H4. unfold mem in H4.
  assert (forall l x, ((if in_dec N.eq_dec x l then true else false) = true) <-> In x l). {
  intros. destruct (in_dec N.eq_dec x l). split; intros; try(assumption); try(reflexivity).
  split; intros. inversion H5. contradiction. } rewrite H5 in H4. rewrite H5 in H4.
  apply H4. } pose proof (vertices_valid g). pose proof (match_in g v).
  assert (In v (nodeList g)). assert (vIn g v = true). apply H7. exists c. exists g'.
  assumption. unfold vIn in H8. unfold mem in H8.
  match goal with | [H: (if ?x then _ else _) = _ |- _] => destruct x end.
  assumption. inversion H8. pose proof (perm_remove (nodeList g') (nodeList g) v N.eq_dec H8 H5 H3 H6).
  apply Permutation_length in H9. simpl in H9. omega.
Qed.

Lemma matchAny_decr_size: forall {a b : Type} {gr} `{Graph gr} `{LawfulGraph gr} c g' (g: gr a b),
  (c, g') = matchAny g ->
  isEmpty g = false ->
  BinInt.Z.abs_nat (noNodes g') < BinInt.Z.abs_nat (noNodes g).
Proof.
  intros. symmetry in H2. destruct c. destruct p. destruct p. pose proof (matchAny_def g H3).
  repeat (match goal with | [H: exists _, _ |- _] => destruct H | [H: ?x /\ ?y |- _] => destruct H end).
  symmetry in H6.
  rewrite H4 in H2. inversion H2; subst.
  apply (match_decr_size (a2, n, a1, a0) g' g n H6).
Qed.