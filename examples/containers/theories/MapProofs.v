Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Import Data.Map.Internal.
Import GHC.Num.Notations.
Require Import OrdTactic.
Require Import Psatz.
Require Import Tactics.
Set Bullet Behavior "Strict Subproofs".

(** ** Tactics for pointer equality *)

Ltac destruct_ptrEq := lazymatch goal with
  | |- context [if PtrEquality.ptrEq ?x ?y && PtrEquality.ptrEq ?x2 ?y2 then _ else _]
  => let Hpe := fresh "Hpe" in
     let Hpe1 := fresh "Hpe1" in
     let Hpe2 := fresh "Hpe2" in
     destruct (PtrEquality.ptrEq x y && PtrEquality.ptrEq x2 y2) eqn:Hpe;
     [ rewrite andb_true_iff in Hpe;
       destruct Hpe as [Hpe1 Hpe2];
       apply PtrEquality.ptrEq_eq in Hpe1;
       apply PtrEquality.ptrEq_eq in Hpe2;
       subst
     | clear Hpe]
  | |- context [if PtrEquality.ptrEq ?x ?y then _ else _]
  => let Hpe := fresh "Hpe" in
     destruct (PtrEquality.ptrEq x y) eqn:Hpe;
     [ apply PtrEquality.ptrEq_eq in Hpe; subst
     | clear Hpe] 
end.

(** * Tactics for option-valued functions *)

Section oro.
Context {a : Type}.

Definition oro : option a -> option a -> option a :=
  fun x y => match x with
    | Some v => Some v
    | None => y
    end.

Infix "|||" := oro.

Definition ando : option a -> option a -> option a :=
  fun x y =>  match y with None => None | _ => x end.

Infix "&&&" := ando.

Definition diffo : option a -> option a -> option a :=
  fun x y => match y with
    | Some v => None
    | None => x
    end.

Lemma oro_None_l : forall x, None ||| x = x.
Proof. intros. destruct x; reflexivity. Qed.

Lemma oro_None_r : forall x, x ||| None = x.
Proof. intros. destruct x; reflexivity. Qed.

Lemma oro_Some_l : forall x y, Some x ||| y = Some x.
Proof. intros. reflexivity. Qed.

Lemma oro_Some_iff: forall x y v, x ||| y = Some v <-> (x = Some v \/ (x = None /\ y = Some v)).
Proof. intros. destruct x, y; simpl; intuition congruence. Qed.

Lemma ando_None_l : forall x, None &&& x = None.
Proof. intros. destruct x; reflexivity. Qed.

Lemma ando_None_r : forall x, x &&& None = None.
Proof. intros. destruct x; reflexivity. Qed.

Lemma ando_Some_r : forall x y, x &&& Some y = x.
Proof. intros. reflexivity. Qed.

Definition SomeIf (b : bool) (x : a) : option a :=
  if b then Some x else None.

Lemma SomeIf_eq_Some : forall b x y,
  SomeIf b x = Some y <-> b = true /\ x = y.
Proof. intros. destruct b; simpl in *; intuition try congruence. Qed.

Lemma SomeIf_eq_None : forall b x,
  SomeIf b x = None <-> b = false.
Proof. intros. destruct b; simpl in *; intuition try congruence. Qed.

Definition isSome (x : option a) : bool := if x then true else false.

Lemma isSome_oro : forall x y, isSome (x ||| y) = isSome x || isSome y.
Proof. intros. destruct x, y; reflexivity. Qed.

Lemma isSome_ando : forall x y, isSome (x &&& y) = isSome x && isSome y.
Proof. intros. destruct x, y; reflexivity. Qed.

Lemma isSome_SomeIf : forall b x, isSome (SomeIf b x) = b.
Proof. intros. destruct b; reflexivity. Qed.


End oro.
Infix "|||" := oro.
Infix "&&&" := ando.

Ltac simpl_options := repeat lazymatch goal with
  | |- context [true    ||  ?x]              => rewrite (orb_true_l x)
  | H: context [true    ||  ?x]         |- _ => rewrite (orb_true_l x) in H
  | |- context [?x      ||  true]            => rewrite (orb_true_r x)
  | H: context [?x      ||  true]       |- _ => rewrite (orb_true_r x) in H
  | |- context [false   ||  ?x]              => rewrite (orb_false_l x)
  | H: context [false   ||  ?x]         |- _ => rewrite (orb_false_l x) in H
  | |- context [?x      ||  false]           => rewrite (orb_false_r x)
  | H: context [?x      ||  false]      |- _ => rewrite (orb_false_r x) in H
  | |- context [None    ||| ?x]              => rewrite (oro_None_l x)
  | H: context [None    ||| ?x]         |- _ => rewrite (oro_None_l x) in H
  | |- context [?x      ||| None]            => rewrite (oro_None_r x)
  | H: context [?x      ||| None]       |- _ => rewrite (oro_None_r x) in H
  | |- context [Some ?x ||| ?y]              => rewrite (oro_Some_l x y)
  | H: context [Some ?x ||| ?y]         |- _ => rewrite (oro_Some_l x y) in H
  | |- context [None    &&& ?x]              => rewrite (ando_None_l x)
  | H: context [None    &&& ?x]         |- _ => rewrite (ando_None_l x) in H
  | |- context [?x      &&& None]            => rewrite (ando_None_r x)
  | H: context [?x      &&& None]       |- _ => rewrite (ando_None_r x) in H
  | |- context [?x      &&& Some ?y]         => rewrite (ando_Some_r x y)
  | H: context [?x      &&& Some ?y]    |- _ => rewrite (ando_Some_r x y) in H
  | |- context [isSome (?x &&& ?y)]          => rewrite (isSome_ando x y)
  | H: context [isSome (?x &&& ?y)]     |- _ => rewrite (isSome_ando x y) in H
  | |- context [isSome (?x ||| ?y)]          => rewrite (isSome_oro x y)
  | H: context [isSome (?x ||| ?y)]     |- _ => rewrite (isSome_oro x y) in H
  | |- context [isSome (Some ?x)]            => simpl (isSome (Some x))
  | H: context [isSome (Some ?x)]       |- _ => simpl (isSome (Some x)) in H
  | |- context [isSome None]                 => simpl (isSome None)
  | H: context [isSome None]            |- _ => simpl (isSome None) in H
  | |- context [isSome (SomeIf ?b ?x)]       => rewrite (isSome_SomeIf b x)
  | H: context [isSome (SomeIf ?b ?x)]  |- _ => rewrite (isSome_SomeIf b x) in H
  | |- context [SomeIf false ?x]             => simpl (SomeIf false x)
  | H: context [SomeIf false ?x]        |- _ => simpl (SomeIf false x) in H
  | |- context [SomeIf true ?x]              => simpl (SomeIf true  x)
  | H: context [SomeIf true ?x]         |- _ => simpl (SomeIf true  x) in H
  | |- context [SomeIf ?b ?x = Some ?y]      => rewrite (SomeIf_eq_Some b x y)
  | H: context [SomeIf ?b ?x = Some ?y] |- _ => rewrite (SomeIf_eq_Some b x y) in H; destruct H; subst
  | |- context [SomeIf ?b ?x = None]         => rewrite (SomeIf_eq_None b x)
  | H: context [SomeIf ?b ?x = None]    |- _ => rewrite (SomeIf_eq_None b x) in H; subst
end; lazy match in *.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Utilities for working with [Ord] *)

(* We don’t have a OrdLawful class yet. We need to introduce that,
   add it to the context, and derive all axioms from that.
 *)
Lemma compare_Eq : forall (x y : e),
  compare x y = Eq <-> x == y = true.
Proof. order e. Qed.
Lemma compare_Lt : forall (x y : e),
  compare x y = Lt <-> x < y = true.
Proof. order e. Qed.
Lemma compare_Gt : forall (x y : e),
  compare x y = Gt <-> x > y = true.
Proof. order e. Qed.

Lemma lt_eq_r : forall x y z,
  x < y = true ->
  z == y = true ->
  x < z = true.
Proof. order e. Qed.

Lemma lt_eq_l : forall x y z,
  x < y = true ->
  z == x = true ->
  z < y = true.
Proof. order e. Qed.

Lemma lt_not_eq : forall (x y : e),
  x < y = true -> x == y = false.
Proof. order e. Qed.

Lemma gt_not_eq : forall (x y : e),
 x > y = true -> x == y = false.
Proof. order e. Qed.


Lemma lt_gt : forall (x y : e), (x > y) = (y < x).
Proof. order e. Qed.

Lemma lt_trans : forall (x y z : e),
  x < y = true -> y < z = true -> x < z = true.
Proof. order e. Qed.


(** This is just like size, but with a type signature that does not confuse [lia] *)
Definition size (s : Map e a) : Z :=
  match s with | Bin sz _ _ _ _ => sz
               | Tip => 0 end.

Lemma size_size: Internal.size = size.
Proof. reflexivity. Qed.

(** * Well-formedness *)

(* Bounds may be absent (infinity) *)
Definition bound := (option e)%type.

(** A suitable comparision operator for bounds.
   If someone feels like it, then you may introduce nice notation. *)
Definition isLB : bound -> e -> bool :=
  fun lb e => match lb with
    | Some lb => lb < e
    | None => true
  end.

Definition isUB : bound -> e -> bool :=
  fun ub e => match ub with
    | Some ub => e < ub
    | None => true
  end.

Ltac order_Bounds :=
  intros;
  simpl isUB in *;
  simpl isLB in *;
  repeat (congruence || lazymatch goal with
    | H : isUB ?ub _ = false |- _ => destruct ub; simpl isUB in *
    | |-  isUB ?ub _ = _          => destruct ub; simpl isUB in *
    | H : isLB ?lb _ = false |- _ => destruct lb; simpl isLB in *
    | |-  isLB ?lb _ = _          => destruct lb; simpl isLB in *
   end);
   order e.

Lemma isLB_lt:
  forall lb x y,
  isLB lb x = true->
  x < y = true ->
  isLB lb y = true.
Proof. order_Bounds. Qed.

Lemma isUB_lt:
  forall ub x y,
  isUB ub x = true->
  y < x = true ->
  isUB ub y = true.
Proof. order_Bounds. Qed.

(** The balancing property of a binary node *)
Definition balance_prop sz1 sz2 :=
  (sz1 + sz2 <= 1 \/ sz1 <= delta * sz2 /\ sz2 <= delta * sz1)%Z.

(** One precondition for [balanceL]: The left tree has been inserted to (but not by too much).
    This is mechanically derived from the context in the call to [balanceL] in [link], and
    unfortunately not very educational.
 *)
Definition balance_prop_inserted sz1 sz2 :=
  (delta * sz1 <= delta*delta*sz2 + delta*sz2 + sz2 /\ sz2 <= sz1)%Z.

(* NB: this does not work: 
Definition balance_prop_inserted sz1 sz2 := balance_prop sz1 sz2.
*)

Fixpoint sem (s : Map e a) (i : e) : option a :=
  match s with | Bin _ x v s1 s2 => sem s1 i ||| SomeIf (i == x) v ||| sem s2 i
               | Tip => None end.

Lemma sem_resp_eq : forall s i j,
  i == j = true -> sem s i = sem s j.
Proof.
  intros.
  induction s.
  * simpl.
    rewrite IHs1, IHs2.
    replace (j == k) with (i == k) by order e.
    reflexivity.
  * reflexivity.
Qed.

(** This inductive predicate describes when sets are well-formed within 
  (exclusive) bounds.
*)


Inductive Bounded : Map e a -> bound -> bound -> Prop :=
  | BoundedTip : forall lb ub,
    Bounded Tip lb ub
  | BoundedBin :
    forall lb ub,
    forall s1,
    forall s2,
    forall x v sz,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true ->
    sz = (1 + size s1 + size s2)%Z ->
    balance_prop (size s1) (size s2) ->
    Bounded (Bin sz x v s1 s2) lb ub.

(** ** Lemmas related to well-formedness *)

(** There are no values outside the bounds *)
Lemma sem_outside_below:
  forall {s lb ub i},
  Bounded s lb ub ->
  isLB lb i = false ->
  sem s i = None.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H2.
  rewrite IHHD2 by order_Bounds.
  simpl_options.
  order_Bounds.
Qed.

Lemma sem_outside_above:
  forall {s lb ub i},
  Bounded s lb ub ->
  isUB ub i = false ->
  sem s i = None.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H2.
  rewrite IHHD1 by order_Bounds.
  simpl_options.
  order_Bounds.
Qed.

Lemma sem_inside:
  forall {s lb ub i v},
  Bounded s lb ub ->
  sem s i = Some v ->
  isLB lb i = true /\ isUB ub i = true.
Proof.
  intros ????? HD ?.
  induction HD; intros; subst; simpl in *; rewrite ?oro_Some_iff in H; intuition; try congruence;
  simpl_options;
  order_Bounds.
Qed.

Lemma sem_inside_isSome:
  forall {s lb ub i},
  Bounded s lb ub ->
  isSome (sem s i) = true ->
  isLB lb i = true /\ isUB ub i = true.
Proof.
  intros ???? HD ?.
  destruct (sem s i) eqn:H1; simpl in *; try congruence.
  eapply sem_inside; eassumption.
Qed.

(* We use this as a rewrite rule because
   [simpl (size (Bin _ _ _ _ ))]
   simplifies the [ 1 + _ ] which is annoying. *)
Lemma size_Bin: forall sz x v (s1 s2 : Map e a),
  size (Bin sz x v s1 s2) = sz.
Proof. intros. reflexivity. Qed.

(* Pose the proof [prf], unless it already exists. *)
Ltac pose_new prf :=
  let prop := type of prf in
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => pose proof prf
  end.

(* Pose the [prop], using [prf], unless it already exists. *)
Ltac assert_new prop prf :=
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => assert prop by prf
  end.

Lemma size_nonneg:
  forall {s lb ub},
  Bounded s lb ub -> (0 <= size s)%Z.
Proof.
  intros ??? HD.
  induction HD.
  * simpl. lia.
  * simpl. lia.
Qed.


Ltac postive_sizes :=
  repeat match goal with [ H : Bounded ?s _ _ |- _ ] => pose_new (size_nonneg H) end.

Lemma size_0_iff_tip:
  forall {s lb ub},
  Bounded s lb ub -> (size s = 0)%Z <-> s = Tip.
Proof.
  induction 1.
  * intuition.
  * postive_sizes;
    rewrite ?size_Bin in *.
    intuition try (congruence || lia).
Qed.

Lemma Bounded_change_ub:
  forall s lb ub ub',
  Bounded s lb (Some ub) ->
  ub <= ub' = true ->
  Bounded s lb (Some ub').
Proof.
  intros ???? HD Heq.
  remember (Some ub) as ubo.
  induction HD; subst.
  * apply BoundedTip; auto.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

Lemma Bounded_change_lb:
  forall s lb lb' ub,
  Bounded s (Some lb) ub ->
  lb' <= lb = true ->
  Bounded s (Some lb') ub.
Proof.
  intros ???? HD Heq.
  remember (Some lb) as lbo.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

(* Bounded_change_ub and Bounded_relax_ub could be united with
   a isNonStrictUB predicate *)
Lemma Bounded_relax_ub:
  forall s lb ub ub',
  Bounded s lb (Some ub) ->
  isUB ub' ub = true ->
  Bounded s lb ub'.
Proof.
  intros ???? HD Heq.
  remember (Some ub) as ubo.
  induction HD; subst.
  * apply BoundedTip; auto.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

Lemma Bounded_relax_lb:
  forall s lb lb' ub,
  Bounded s (Some lb) ub ->
  isLB lb' lb = true ->
  Bounded s lb' ub.
Proof.
  intros ???? HD Heq.
  remember (Some lb) as lbo.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

Lemma Bounded_relax_ub_None:
  forall s lb ub,
  Bounded s lb ub ->
  Bounded s lb None.
Proof.
  intros ??? HD.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * eapply BoundedBin; try eassumption; try reflexivity.
Qed.

Lemma Bounded_relax_lb_None:
  forall s lb ub,
  Bounded s lb ub ->
  Bounded s None ub.
Proof.
  intros ??? HD.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * eapply BoundedBin; try eassumption; try reflexivity.
Qed.


(** ** Tactics for Boundedness etc. *)


(** Learns bounds of values found in some set in the context *)
Ltac inside_bounds :=
  repeat lazymatch goal with
    | H : Bounded ?s _ _, H2 : sem ?s ?i = Some _ |- _ =>
       apply (sem_inside H) in H2; destruct H2
    | H : Bounded ?s _ _, H2 : isSome (sem ?s ?i) = true |- _ =>
       apply (sem_inside_isSome H) in H2; destruct H2
  end.

(** Solve [isLB] and [isUB] goals.  *)
Ltac solve_Bounds := first
  [ eassumption
  | solve [inside_bounds; order_Bounds]
  | idtac "solve_Bounds gave up"
  ].

(* Solve equations of the form
     forall i, f i = f0 i || f1 i
   possibly using equations from the context.
   Fails if it does not start with [forall i,], but may leave a partially solve goal.
    *)
Ltac f_solver_simple  :=
  let i := fresh "i" in 
  intro i;
  try reflexivity; (* for when we have an existential variable *)
  repeat multimatch goal with [ H : (forall i, _) |- _] => specialize (H i) end;
  repeat match goal with [ H : ?f = _ |- context [?f i] ] => rewrite H in *; clear H end;
  simpl sem in *; simpl_options;
  try reflexivity.


(** This auxillary tactic destructs one boolean or option atom in the argument *)

Ltac split_bool_go expr :=
  lazymatch expr with 
    | true       => fail
    | false      => fail
    | Some _     => fail
    | None       => fail
    | match ?x with _ => _ end => split_bool_go x || (simpl x; cbv match)
    | negb ?x      => split_bool_go x
    | ?x && ?y     => split_bool_go x || split_bool_go y
    | ?x || ?y     => split_bool_go x || split_bool_go y
    | xorb ?x ?y   => split_bool_go x || split_bool_go y
    | ?x ||| ?y    => split_bool_go x || split_bool_go y
    | ?x &&& ?y    => split_bool_go x || split_bool_go y
    | diffo ?x ?y  => split_bool_go y || split_bool_go x
    | SomeIf ?b ?x => split_bool_go b
    | ?bexpr       => destruct bexpr eqn:?
  end.

(** This auxillary tactic destructs one boolean or option atom in the goal *)


Ltac split_bool :=
  match goal with 
    | |- ?lhs = ?rhs        => split_bool_go lhs || split_bool_go rhs
    (* A bit ad-hoc, could be improved: *)
    | H : ?x ||| ?y = Some _   |- _ => split_bool_go x
    | H : ?x ||| ?y = None     |- _ => split_bool_go x
    | H : context [?x &&& ?y]  |- _ => split_bool_go y
    | H : context [?x &&& ?y]  |- _ => split_bool_go y
    | H : diffo ?x ?y = Some _ |- _ => split_bool_go y
    | H : diffo ?x ?y = None   |- _ => split_bool_go y
    | H : ?x || ?y = true      |- _ => split_bool_go x
    | H : ?x || ?y = false     |- _ => split_bool_go x
    | H : ?x && ?y = true      |- _ => split_bool_go x
    | H : ?x && ?y = false     |- _ => split_bool_go x
  end.


Ltac f_solver_cleanup :=
  simpl negb in *;
  simpl_options;
  try congruence;
  repeat lazymatch goal with
    |  H1 : true   = true   |- _ => clear H1
    |  H1 : true   = _      |- _ => symmetry in H1
    |  H1 : false  = false  |- _ => clear H1
    |  H1 : false  = _      |- _ => symmetry in H1
    |  H1 : Some _ = Some _ |- _ => inversion H1; subst; clear H1
    |  H1 : Some _ = _      |- _ => symmetry in H1
    |  H1 : None   = None   |- _ => clear H1
    |  H1 : None   = _      |- _ => symmetry in H1
  end;
  (* Find equalities *)
  repeat lazymatch goal with
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = Some ?a, H3 : sem ?s ?j = Some ?b |- _
      => rewrite (sem_resp_eq s i j H1) in H2; rewrite H2 in H3; inversion H3; subst; clear H3
  end;
  (* Try to solve it *)
  try solve [exfalso; inside_bounds; order_Bounds];
  try reflexivity;
  (* Find conradiction *)   
  try lazymatch goal with
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = Some _, H3 : sem ?s ?j = None |- _
      => exfalso; rewrite (sem_resp_eq s i j H1) in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : isSome (sem ?s ?i) = true, H3 : sem ?s ?j = None |- _
      => exfalso; rewrite <- (sem_resp_eq s i j H1) in H3; rewrite H3 in H2; simpl in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : isSome (sem ?s ?i) = false, H3 : sem ?s ?j = Some _ |- _
      => exfalso; rewrite <- (sem_resp_eq s i j H1) in H3; rewrite H3 in H2; simpl in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = None, H3 : sem ?s ?j = Some _ |- _
      => exfalso; rewrite (sem_resp_eq s i j H1) in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = None, H3 : isSome (sem ?s ?j) = true |- _
      => exfalso; rewrite  (sem_resp_eq s i j H1) in H2; rewrite H2 in H3; simpl in H3; congruence
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = Some _, H3 : isSome (sem ?s ?j) = false |- _
      => exfalso; rewrite  (sem_resp_eq s i j H1) in H2; rewrite H2 in H3; simpl in H3; congruence
  end.

Ltac f_solver_step := first
  [ split_bool
  | lazymatch goal with H : context [if ?x == ?y then _ else _] |- _
      => destruct (x == y) eqn:?
    end
(*   | exfalso *)
  ].

Ltac f_solver := f_solver_simple; f_solver_cleanup; repeat (f_solver_step; f_solver_cleanup).

(** A variant of [lia] that unfolds a few specific things and knows that
   the size of a well-formed tree is positive. *)
Ltac lia_sizes :=
  postive_sizes;
  unfold balance_prop_inserted, balance_prop, delta, ratio in *;
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__,
                      Num_Integer__, Ord_Integer___,
                      op_zg____, op_zl____ in *;
  rewrite ?size_size in *;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  lia.

(** A tactic to solve questions about size. *)
Ltac solve_size := first
  [ assumption
  | reflexivity
  | lia_sizes
  | idtac "solve_size gave up"
  ].

(** Solve goals of Bounded. Should be back-tracking free, I think. *)
Ltac solve_Bounded := eassumption || lazymatch goal with
  | [ |- Bounded Tip _ _ ]
    => apply BoundedTip
  | [ H : Bounded ?s ?lb (Some ?ub) |- Bounded ?s ?lb (Some ?ub') ]
    => apply (Bounded_change_ub _ _ _ _ H); solve_Bounds
  | [ H : Bounded ?s (Some ?lb) ?ub  |- Bounded ?s (Some ?lb') ?ub ]
    => apply (Bounded_change_lb _ _ _ _ H); solve_Bounds
  | [ H : Bounded ?s ?lb (Some ?ub) |- Bounded ?s ?lb ?ub' ]
    => apply (Bounded_relax_ub _ _ _ _ H); solve_Bounds
  | [ H : Bounded ?s (Some ?lb) ?ub  |- Bounded ?s ?lb' ?ub ]
    => apply (Bounded_relax_lb _ _ _ _ H); solve_Bounds
  | [ |- Bounded (Bin _ _ _ _ _) _ _ ]
    => apply BoundedBin;
        [ solve_Bounded
        | solve_Bounded
        | solve_Bounds
        | solve_Bounds
        | solve_size
        | solve_size
        ]
  | |- ?H => fail "solve_Bounded gave up on" H
  end.

(** We now have special tactics for the three kinds of preconditions most
    our lemmas below have. So we can write a tactic that correctly chooses the
    right tactic.
    Why not simply use [first [solve_Bounded|solve_Bounds|solve_size]]?
    Because that would involve backtracking which hides error messages from us,
    and is possibly too slow.
  *)

Ltac solve_Precondition := lazymatch goal with
  | |- Bounded _ _ _          => solve_Bounded
  | |- isLB _ _ = true        => solve_Bounds
  | |- isUB _ _ = true        => solve_Bounds
  | |- context [map_size]     => simpl; lia    (* in well-founded recursion *)
  | |- _ = _                  => solve_size
  | |- context [balance_prop] => solve_size
  | |- ?H                     => fail "solve_Precondition does not recognize this goal: " H
  end.

(** ** A setup for complete specification *)



(** A proposition of the form [Desc s lb ub sz f] tells us
  everything we need to know about [s].

  Therefore, it is phrased as an induction lemma which replaces
  the concrete Set (e.g. [insert y s]) with a fresh variable [s'],
  and adds all interesting bits about it to the context.

  To prove a [Desc] statement, use [apply showDesc].

  To use a [Desc] statement, use [applyDesc HD] or [apply foo_Desc].
  *)

Definition Desc s lb ub sz f : Prop :=
  forall (P : Map e a -> Prop),
  (forall s,
    Bounded s lb ub ->
    size s = sz ->
    (forall i, sem s i = f i) ->
    P s) ->
  P s.

Local Inductive HIDE (P : Prop) := unhide : P -> HIDE P.
Local Lemma hide : forall {P : Prop},  HIDE P -> P. Proof. intros. inversion H. assumption. Qed.

Ltac applyDesc lem :=
  apply hide;
  eapply lem;
  [ solve_Precondition ..
  | let s := fresh "s" in 
    let HB := fresh "HB" in
    let Hsz := fresh "Hsz" in
    let Hsem := fresh "Hsem" in
    intros s HB Hsz Hsem;
    apply unhide;
    try replace (size s) in *;
    try replace (sem s) in *;
    try assumption
  ].

Lemma showDesc :
  forall s lb ub sz f,
  Bounded s lb ub /\ size s = sz /\ (forall i, sem s i = f i) ->
  Desc s lb ub sz f.
Proof.
  intros. intros P HP. apply HP; intuition.
Qed.

Lemma Desc_change_f:
  forall s lb ub sz f f',
  (forall i, f' i = f i) ->
  Desc s lb ub sz f' <-> Desc s lb ub sz f.
Proof.
  intros.
  split; intro HD; applyDesc HD;
  (apply showDesc; split; [solve_Bounded | split; [solve_size | simpl sem; try solve [f_solver]]]);
  intuition.
Qed.

(** A variant that does not indicate anything about [size]. *)

Definition Desc' s lb ub f : Prop :=
  forall (P : Map e a -> Prop),
  (forall s,
    Bounded s lb ub ->
    True ->             (* So that we can still use [applyDesc] here *)
    (forall i, sem s i = f i) ->
    P s) ->
  P s.

Lemma showDesc' :
  forall s lb ub f,
  Bounded s lb ub /\ (forall i, sem s i = f i) ->
  Desc' s lb ub f.
Proof.
  intros. intros P HP. apply HP; intuition.
Qed.

Ltac solve_Desc :=
 lazymatch goal with
 | |- (Desc _ _ _ _ _)
 => apply showDesc; split; [solve_Bounded | split; [solve_size | simpl sem; try solve [f_solver]]]
 | |- (Desc' _ _ _ _)
 => apply showDesc'; split; [solve_Bounded | simpl sem; try solve [f_solver]]
 | |- ?P
 => fail "solve_Desc: Goal not a Desc or Desc' proposition: " P
 end.

(** ** The actual [WF] predicate *)


(** And any set that has a bounds is well-formed *)
Definition WF (s : Map e a) : Prop := Bounded s None None.

Lemma Desc_WF:
  forall s sz f,
  Desc s None None sz f -> WF s.
Proof.
  intros ??? HD.
  unfold WF.
  (* Unfortunately, [apply HD] does not work unless we have [size s] and [sem s]
     in the context. *)
  assert (Bounded s None None /\ size s = size s /\ sem s = sem s) by (apply HD; auto).
  intuition.
Qed.


(** For every set in the context, try to see if [lia] knows it is empty. *)
Ltac find_Tip :=
  match goal with [ H : Bounded ?s _ _ |- _ ] =>
    assert_new (size s = 0)%Z lia_sizes;
    rewrite (size_0_iff_tip H) in *;
    subst s;
    inversion H;
    clear H;
    subst
  end.

Require Import Coq.Program.Tactics.

Open Scope Z_scope.

(** ** Verification of [empty] *)

Lemma empty_Desc:
  forall lb ub,
  Desc empty lb ub 0 (fun _ => None).
Proof. intros. unfold empty. solve_Desc. Qed.

Lemma empty_WF: WF empty.
Proof. intros. unfold empty. eapply Desc_WF. apply empty_Desc. Qed.


(** ** Verification of [null] *)

Lemma null_spec:
  forall s, WF s -> null s = true <-> s = Tip.
Proof. intros. unfold null. inversion H; simpl; intuition (congruence || lia_sizes). Qed.


(** ** Verification of [singleton] *)

Lemma singleton_Desc:
  forall x v lb ub,
  isLB lb x = true ->
  isUB ub x = true ->
  Desc (singleton x v) lb ub 1 (fun i => SomeIf (i == x) v).
Proof.
  intros.

  unfold singleton.
  unfold fromInteger, Num_Integer__.
  solve_Desc.
Qed.


Lemma singleton_WF:
  forall x v, WF (singleton x v).
Proof. intros. eapply Desc_WF. eapply singleton_Desc; reflexivity. Qed.

(** ** Verifying the various balancing operations *)

(** *** Verification of [balanceL] *)

Lemma balanceL_Desc:
    forall x v s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) \/
    balance_prop_inserted (size s1 - 1) (size s2) /\ (1 <= size s1)%Z \/
    balance_prop (size s1) (size s2 + 1) ->
    Desc (balanceL x v s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i ||| SomeIf (i == x) v ||| sem s2 i).
Proof.
  intros.

  unfold balanceL.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [solve_Desc].
Qed.

(** *** Verification of [balanceR] *)

Lemma balanceR_Desc:
    forall x v s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) \/
    balance_prop_inserted (size s2 - 1) (size s1) /\ (1 <= size s2)%Z  \/
    balance_prop (size s1 + 1) (size s2) ->
    Desc (balanceR x v s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i ||| SomeIf (i == x) v ||| sem s2 i).
Proof.
  intros.

  unfold balanceR.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [solve_Desc].
Qed.

(** *** Verification of [insertMax] *)

Lemma insertMax_Desc:
    forall x v s1 lb ub,
    Bounded s1 lb (Some x) ->
    isLB lb x = true ->
    isUB ub x = true->
    Desc (insertMax x v s1) lb ub (1 + size s1) (fun i => sem s1 i ||| SomeIf (i == x) v).
Proof.
  intros.
  
  remember (Some x) as ub'. revert dependent x.
  induction H; intros; subst; cbn - [Z.add SomeIf].
  * applyDesc singleton_Desc.
    solve_Desc.
  * clear IHBounded1.
    applyDesc IHBounded2.
    applyDesc balanceR_Desc.
    solve_Desc.
Qed.

(** *** Verification of [insertMin] *)

Lemma insertMin_Desc:
    forall x v s2 lb ub,
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    Desc (insertMin x v s2) lb ub (1 + size s2) (fun i => SomeIf (i == x) v ||| sem s2 i).
Proof.
  intros.
  remember (Some x) as ub'. revert dependent x.
  induction H; intros; subst; cbn - [Z.add].
  * applyDesc singleton_Desc.
    solve_Desc.
  * clear IHBounded2.
    applyDesc IHBounded1.
    applyDesc balanceL_Desc.
    solve_Desc.
Qed.

(** *** Verification of [link] *)

Lemma link_eq (x : e) (v : a) (s1: Map e a)  (s2: Map e a) :
  link x v s1 s2 =
       match s1, s2 with
          | Tip , r => insertMin x v r
          | l , Tip => insertMax x v l
          | (Bin sizeL y vy ly ry as l) , (Bin sizeR z vz lz rz as r) =>
            if Sumbool.sumbool_of_bool ((delta GHC.Num.* sizeL) GHC.Base.< sizeR)
            then balanceL z vz (link x v l lz) rz
            else if Sumbool.sumbool_of_bool  ((delta GHC.Num.* sizeR) GHC.Base.< sizeL)
                 then balanceR y vy ly (link x v ry r)
                 else bin x v l r
        end.
Proof.
  destruct s1; [|reflexivity].
  destruct s2; [|reflexivity].
  unfold link at 1, link_func at 1.
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.

(* [program_simpl] calls [simpl], which is very confusing due to [1 + _]. So
ask [Next Obligation] to use this only when it solves the goal completely. *)
Local Obligation Tactic := try solve [program_simpl].

Program Fixpoint link_Desc (x : e) (v : a) (s1: Map e a) (s2: Map e a)
  {measure (map_size s1 + map_size s2)} :
    forall lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    Desc (link x v s1 s2) lb ub (1 + size s1 + size s2)
        (fun i => sem s1 i ||| SomeIf (i == x) v ||| sem s2 i)
    := _.
Next Obligation.
  intros.
  rewrite link_eq. 
  inversion H; subst; clear H;
  inversion H0; subst; clear H0.
  * simpl insertMin.
    applyDesc singleton_Desc.
    solve_Desc.
  * applyDesc insertMin_Desc.
    solve_Desc.
  * applyDesc insertMax_Desc.
    solve_Desc.
  * destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
    - applyDesc link_Desc.
      applyDesc balanceL_Desc.
      solve_Desc.
    - applyDesc link_Desc.
      applyDesc balanceR_Desc.
      solve_Desc.
    - clear link_Desc.
      unfold bin.
      solve_Desc.
Qed.

(** ** Verification of [lookup] *)

Lemma lookup_spec:
 forall {s lb ub i}, Bounded s lb ub -> lookup i s = sem s i.
Proof.
  intros ???? HB.
  induction HB.
  * simpl. reflexivity.
  * subst; simpl.
    destruct (compare i x) eqn:?.
    + replace (i == x) with true by order_Bounds.
      rewrite (sem_outside_above HB1) by order_Bounds.
      reflexivity.
    + replace (i == x) with false by order_Bounds.
      rewrite IHHB1.
      rewrite (sem_outside_below HB2) by order_Bounds.
      simpl_options.
      reflexivity.
    + replace (i == x) with false by order_Bounds.
      rewrite IHHB2.
      rewrite (sem_outside_above HB1) by order_Bounds.
      simpl_options.
      reflexivity.
Qed.


(** ** Verification of [insert] *)

(* The [orig] passing and the local fixpoint in insert is plain ugly, so let’s to this instead *)

Fixpoint insert' (x : e) (v : a) (s : Map e a) : Map e a :=
  match s with 
    | Tip => singleton x v
    | Bin sz y vy l r => match compare x y with
      | Lt =>
        let l' := insert' x v l in
        if PtrEquality.ptrEq l' l then s else balanceL y vy l' r
      | Gt =>
        let r' := insert' x v r in 
        if PtrEquality.ptrEq r' r then s else balanceR y vy l r'
      | Eq =>
        if PtrEquality.ptrEq v vy && PtrEquality.ptrEq x y then s else Bin sz x v l r
     end
  end.

Lemma insert_insert' : forall x v s, insert x v s = insert' x v s.
Proof.
  intros.
  unfold insert.
  induction s; simpl.
  * destruct (compare x k).
    - reflexivity.
    - rewrite IHs1. reflexivity.
    - rewrite IHs2. reflexivity.
  * reflexivity.
Qed.

Lemma insert_Desc:
  forall y v s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insert y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
      (fun i => (if i == y then Some v else None) ||| sem s i).
Proof.
  intros ????? HB HLB HUB.
  rewrite insert_insert'.
  induction HB; intros.
  * simpl.
    applyDesc singleton_Desc; try eassumption; solve_Desc.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      rewrite Heqc.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      destruct_ptrEq.
      - solve_Desc.
      - unfold Datatypes.id.
        solve_Desc.
    + clear IHHB2.
      applyDesc IHHB1.

      rewrite (sem_outside_below HB2) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      simpl_options.

      destruct_ptrEq.
      - destruct (sem s1 y) eqn:?; simpl isSome in *; try lia.
        solve_Desc.
      - destruct (sem s1 y); simpl isSome in *;
        applyDesc balanceL_Desc;
        cbv match in *;
        solve_Desc.
    + (* more or less a copy-n-paste from above *)
      clear IHHB1.
      applyDesc IHHB2.

      rewrite (sem_outside_above HB1) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      simpl_options.

      destruct_ptrEq.
      - destruct (sem s2 y) eqn:?; simpl_options; try lia.
        solve_Desc.
      - destruct (sem s2 y); simpl_options;
        applyDesc balanceR_Desc;
        solve_Desc.
Qed.

(** ** Verification of [insertR] *)

Fixpoint insertR' (x : e) (v : a) (s : Map e a) : Map e a :=
  match s with 
    | Tip => singleton x v
    | Bin sz y vy l r => match compare x y with
      | Lt =>
        let l' := insertR' x v l in
        if PtrEquality.ptrEq l' l then s else balanceL y vy l' r
      | Gt =>
        let r' := insertR' x v r in 
        if PtrEquality.ptrEq r' r then s else balanceR y vy l r'
      | Eq => Bin sz y vy l r
     end
  end.

Lemma insertR_insertR' : forall x v s, insertR x v s = insertR' x v s.
Proof.
  intros.
  unfold insertR.
  induction s; simpl.
  * destruct (compare x k).
    - reflexivity.
    - rewrite IHs1. reflexivity.
    - rewrite IHs2. reflexivity.
  * reflexivity.
Qed.


Lemma insertR_Desc:
  forall y v s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insertR y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
    (fun i => sem s i ||| (if i == y then Some v else None)).
Proof.
  intros ????? HB HLB HUB.

  rewrite insertR_insertR'.
  induction HB; intros.
  * simpl.
    applyDesc singleton_Desc; try eassumption; solve_Desc.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      rewrite Heqc.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      solve_Desc.
    + clear IHHB2.
      applyDesc IHHB1.

      rewrite (sem_outside_below HB2) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      simpl_options.

      destruct_ptrEq.
      - destruct (sem s1 y) eqn:?; simpl_options; try lia.
        solve_Desc.
      - destruct (sem s1 y); simpl_options;
        applyDesc balanceL_Desc;
        solve_Desc.
    + (* more or less a copy-n-paste from above *)
      clear IHHB1.
      applyDesc IHHB2.

      rewrite (sem_outside_above HB1) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      simpl_options.
      
      destruct_ptrEq.
      - destruct (sem s2 y) eqn:?; simpl_options; try lia.
        solve_Desc.
      - destruct (sem s2 y); simpl_options;
        applyDesc balanceR_Desc;
        solve_Desc.
Qed.


Lemma insert_WF:
  forall y v s, WF s -> WF (insert y v s).
Proof. intros. eapply Desc_WF. eapply insert_Desc; try reflexivity; try assumption. Qed.

(** ** Verification of [maxViewSure] *)

Lemma maxViewSure_Desc:
  forall sz' x v s1 s2 lb ub,
    Bounded (Bin sz' x v s1 s2) lb ub ->
    forall P,
    (forall y vy r,
      (y = x /\ vy = v \/ sem s2 y = Some vy) /\
      Desc r lb (Some y) (size s1 + size s2)
                         (fun i => if i == y then None else (sem s1 i ||| (if i == x then Some v else None) ||| sem s2 i)) ->
      P (Mk_MaxView y vy r)) ->
    P (maxViewSure x v s1 s2).
    (* we know that y is in the input, and we actually know more: it is x or in s2 *)
Proof.
  intros ??????? HB.
  revert sz' x v s1 lb ub HB.
  induction s2; intros sz' x v s1 lb ub HB;subst.
  - clear IHs2_1.
    simpl.
    intros X HX.
    destruct (maxViewSure k a0 s2_1 s2_2) eqn:HmaxView.
    apply HX. clear X HX.

    inversion HB; subst; clear HB.
    inversion H5; subst.

    revert HmaxView.
    eapply IHs2_2; only 1: solve_Bounded.
    intros y vy r H; destruct H as [Hthere IHD]; clear IHs2_2.
    cbn -[Z.add size] in *; rewrite size_Bin in *.

    intro HmaxView; inversion HmaxView; subst; clear HmaxView.

    applyDesc IHD; clear IHD.

    split.
    + right.
      destruct Hthere as [[H H2]|H]; rewrite H in *.
      * subst. rewrite Eq_refl.
        erewrite sem_outside_above by solve_Bounds.
        reflexivity.
      * erewrite sem_outside_above by solve_Bounds.
        replace (e0 == k) with false by solve_Bounds.
        reflexivity.
    + destruct Hthere as [[Heq Heq1]|Hthere].
      * subst; applyDesc balanceL_Desc; solve_Desc.
      * applyDesc balanceL_Desc.
        solve_Desc.
  - intros X HX.
    destruct (maxViewSure _ _ _ _) eqn:HmaxView.
    apply HX. clear X HX.
    cbn -[Z.add size] in *.
    inversion HB; subst; clear HB.
    inversion HmaxView; subst; clear HmaxView.
    split; [left; (split;reflexivity) | solve_Desc].
Qed.

(** ** Verification of [minViewSure] *)

Lemma minViewSure_Desc:
  forall sz' x v s1 s2 lb ub,
    Bounded (Bin sz' x v s1 s2) lb ub ->
    forall P,
    (forall y vy r,
      (y = x /\ vy = v \/ sem s1 y = Some vy) /\
      Desc r (Some y) ub (size s1 + size s2)
                         (fun i => if i == y then None else (sem s1 i ||| (if i == x then Some v else None) ||| sem s2 i)) ->
      P (Mk_MinView y vy r)) ->
    P (minViewSure x v s1 s2).
    (* we know that y is in the input, and we actually know more: it is x or in s2 *)
Proof.
  intros ??????? HB.
  revert sz' x v s2 lb ub HB.
  induction s1; intros sz' x v s2 lb ub HB;subst.
  - clear IHs1_2.
    simpl.
    intros X HX.
    destruct (minViewSure _ _ _ _ ) eqn:HmaxView.
    apply HX. clear X HX.

    inversion HB; subst; clear HB.
    inversion H4; subst.

    revert HmaxView.
    eapply IHs1_1; only 1: solve_Bounded.
    intros y vy r H; destruct H as [Hthere IHD]; clear IHs1_1.
    cbn -[Z.add size] in *; rewrite size_Bin in *.

    intro HmaxView; inversion HmaxView; subst; clear HmaxView.

    applyDesc IHD; clear IHD.

    split.
    + right.
      destruct Hthere as [[H H2]|H]; rewrite H in *.
      * subst. rewrite Eq_refl.
        erewrite sem_outside_above by solve_Bounds.
        reflexivity.
      * reflexivity.
    + destruct Hthere as [[Heq Heq1]|Hthere].
      * subst; applyDesc balanceR_Desc; solve_Desc.
      * applyDesc balanceR_Desc; solve_Desc.
  - intros X HX.
    destruct (minViewSure _ _ _ _) eqn:Hview.
    apply HX. clear X HX.
    cbn -[Z.add size] in *.
    inversion HB; subst; clear HB.
    inversion Hview; subst; clear Hview.
    split; [left; (split;reflexivity) | solve_Desc].
Qed.

(** ** Verification of [glue] *)

Lemma glue_Desc:
  forall s1 s2 lb ub x,
  Bounded s1 lb (Some x) ->
  Bounded s2 (Some x) ub ->
  isLB lb x = true ->
  isUB ub x = true ->
  balance_prop (size s1) (size s2) ->
  Desc (glue s1 s2) lb ub ((size s1 + size s2)%Z) (fun i => sem s1 i ||| sem s2 i).
Proof.
  intros ????? HB1 HB2 ???.

  inversion HB1; inversion HB2; subst; cbn -[Z.add]; clear HB1 HB2.
  1-3: solve [solve_Desc|solve_size].
  destruct (Z.ltb_spec (1 + size s4 + size s5) (1 + size s0 + size s3)).
  - eapply maxViewSure_Desc; only 1: solve_Bounded.
    intros y vy r [Hthere HD].
    applyDesc HD.
    destruct Hthere as [[??]|Hthere].
    * subst; applyDesc balanceR_Desc; solve_Desc.
    * subst; applyDesc balanceR_Desc; solve_Desc.
  - eapply minViewSure_Desc; only 1: solve_Bounded.
    intros y vy r [Hthere HD].
    applyDesc HD.
    destruct Hthere as [[??]|Hthere]; subst; applyDesc balanceL_Desc; solve_Desc.
Qed.

(** ** Verification of [delete] *)

Lemma delete_Desc :
  forall x s lb ub,
  Bounded s lb ub ->
  Desc (delete x s) lb ub (if isSome (sem s x) then (size s - 1) else size s) (fun i => if i == x then None else sem s i).
Proof.
  intros ???? HB.
  induction HB; intros; subst.
  - simpl. solve_Desc.
  - cbn -[Z.add].
    destruct (compare x x0) eqn:Heq.
    + replace (x == x0) with true by solve_Bounds.
      simpl_options.
      applyDesc glue_Desc.
      solve_Desc.
    + applyDesc IHHB1; clear IHHB1 IHHB2.
      replace (x == x0) with false by solve_Bounds.
      rewrite -> (sem_outside_below HB2) by solve_Bounds.
      simpl_options.
      destruct_ptrEq.
      * replace (isSome (sem s1 x)) with false in *
          by (destruct (sem s1 x); simpl in *;  try congruence; lia).
        solve_Desc.
      * destruct (sem s1 x); cbn -[Z.add] in *; applyDesc balanceR_Desc; solve_Desc.
    + applyDesc IHHB2; clear IHHB1 IHHB2.
      replace (x == x0) with false by solve_Bounds.
      rewrite -> (sem_outside_above HB1) by solve_Bounds.
      simpl_options.
      destruct_ptrEq.
      * replace (isSome (sem s2 x)) with false by (destruct (sem s2 x); simpl in *; try congruence; lia).
        solve_Desc.
      * destruct (sem s2 x); cbn -[Z.add] in *; applyDesc balanceL_Desc; solve_Desc.
Qed.

(** ** Verification of [split] *)

Lemma split_Desc :
  forall x s lb ub,
  Bounded s lb ub ->
  forall (P : Map e a * Map e a -> Prop),
  (forall s1 s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    size s = size s1 + size s2 + (if isSome (sem s x) then 1 else 0) ->
    (forall i, sem s i = (if i == x then sem s i else sem s1 i ||| sem s2 i)) ->
    P (s1, s2)) ->
  P (split x s) : Prop.
Proof.
  intros ?? ?? HB.
  Ltac solveThis := intros X HX; apply HX; clear X HX; [solve_Bounded|solve_Bounded| |f_solver].
  induction HB.
  - solveThis. reflexivity.
  - simpl.
    destruct (compare x x0) eqn:?.
  + solveThis. replace (x == x0) with true by order e.
    simpl_options. lia.
  + apply IHHB1; intros s1_2 s1_3 HB1_2 HB1_3 Hsz Hsems1; clear IHHB1 IHHB2.
    applyDesc link_Desc.
    solveThis. destruct (sem s1 x); cbn -[Z.add] in *.
    * simpl. lia.
    * replace (x == x0) with false by order e. simpl.
      rewrite (sem_outside_below HB2) by solve_Bounds. simpl. lia.
  + apply IHHB2; intros s2_2 s2_3 HB2_2 HB2_3 Hsz Hsems2; clear IHHB1 IHHB2.
    applyDesc link_Desc.
    solveThis. destruct (sem s2 x); cbn -[Z.add] in *.
    * simpl_options. lia.
    * replace (x == x0) with false by order e. simpl.
      rewrite (sem_outside_above HB1) by solve_Bounds. simpl. lia.
Qed.

(** ** Verification of [union] *)

(* The [union] uses some nested pattern match that expand to a very large
   number of patterns in Coq. So let’s take them apart here *)
Lemma union_destruct :
  forall (P : Map e a -> Prop),
  forall s1 s2,
  (s2 = Tip -> P s1) ->
  (s1 = Tip -> P s2) ->
  (forall sz2 x vx, (s2 = Bin sz2 x vx Tip Tip) -> P (insertR x vx s1)) ->
  (forall sz1 x vx, (s1 = Bin sz1 x vx Tip Tip) -> P (insert x vx s2)) ->
  (forall sz1 x vx l1 r1, (s1 = Bin sz1 x vx l1 r1) -> 
    P (
      match split x s2 with
      | pair l2 r2 =>
      match union r1 r2 with
      | r1r2 =>
      match union l1 l2 with
      | l1l2 => if andb  (PtrEquality.ptrEq l1l2 l1)
                         (PtrEquality.ptrEq r1r2 r1) : bool
                then s1 else link x vx l1l2 r1r2
      end end end)) ->
  P (union s1 s2).
Proof.
  intros P s1 s2 HTipR HTipL HSingletonR HSingletonL HBins.
  destruct s1, s2; simpl union;
  try destruct s1_1, s1_2;
  try destruct s2_1, s2_2;
  first [ eapply HBins; reflexivity
        | eapply HSingletonL; reflexivity
        | eapply HSingletonR; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed. 

Lemma union_Desc :
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (union s1 s2) lb ub (fun i => sem s1 i ||| sem s2 i).
(* We use [Desc'] here, because the result of [union] is passed to [link], which
   does a full rebalance, and hence does not need to know anything about the size.
   If it turns out we need [size (union s1 s2)], we can still add it.
*)
Proof.
  intros ???? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  * apply union_destruct; intros; subst; try congruence.
    + solve_Desc.
    + solve_Desc.
    + inversion HB3; subst; clear HB3.
      clear H4 H5.
      (* We need to give [applyDesc] a hint about the bounds that we care about: *)
      assert (Bounded Tip lb ub) by constructor.
      applyDesc insertR_Desc.
      solve_Desc.
  * apply union_destruct; intros; subst; try congruence.
    + solve_Desc.
    + inversion HB3; subst; clear HB3.
      applyDesc insertR_Desc.
      solve_Desc.
    + inversion H3; subst; clear H3.
      applyDesc insert_Desc. solve_Desc.
    + inversion H3; subst; clear H3.
      eapply split_Desc; try eassumption.
      intros.
      applyDesc IHHB1_1.
      applyDesc IHHB1_2.
      destruct_ptrEq.
      - solve_Desc.
      - applyDesc link_Desc.
        solve_Desc.
Qed.

(** ** Verification of [link2] *)

(** This is called  [merge] for Set *)

Lemma link2_eq: forall (l r: Map e a), link2 l r = 
  match l, r with 
  | Tip, r => r
  | l, Tip => l
  | (Bin sizeL x vx lx rx as l), (Bin sizeR y vy ly ry as r) =>
    if Sumbool.sumbool_of_bool
         ((delta GHC.Num.* sizeL) GHC.Base.< sizeR)
    then balanceL y vy (link2 l ly) ry           
    else if Sumbool.sumbool_of_bool
              ((delta GHC.Num.* sizeR) GHC.Base.< sizeL)
         then balanceR x vx lx (link2 rx r)
         else glue l r
  end.
Proof.
  intros l r.
  destruct l; [|auto].
  destruct r; [|auto].
  unfold link2 at 1, link2_func at 1;
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.


Program Fixpoint link2_Desc (s1: Map e a)  (s2: Map e a)
  {measure (map_size s1 + map_size s2)} :
    forall x lb ub,
      Bounded s1 lb (Some x) ->
      Bounded s2 (Some x) ub  ->
      isLB lb x = true ->
      isUB ub x = true->
      Desc (link2 s1 s2) lb ub (size s1 + size s2)
           (fun i => sem s1 i ||| sem s2 i)
  := _.
Next Obligation.
  intros.
  rewrite link2_eq. 
  inversion H; subst; clear H;
    inversion H0; subst; clear H0;
      try solve [solve_Desc].
  destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
  - applyDesc link2_Desc.
    applyDesc balanceL_Desc.
    solve_Desc.
  - applyDesc link2_Desc.
    applyDesc balanceR_Desc.
    solve_Desc.
  - applyDesc glue_Desc.
    solve_Desc.
Qed.


(** ** Verification of [splitMember] *)

(* Rewrite to avoid local [go] and StrictTriple *)
Fixpoint splitMember' (k : e) (s : Map e a) : (Map e a * bool * Map e a)%type :=
  match s with
   | Tip => (Tip, false, Tip)
   | Bin _ kx x l r => match GHC.Base.compare k kx with
     | Lt => match splitMember' k l with
               | (lt, z, gt) => match link kx x gt r with
                                              | gt' => (lt, z, gt')
                                            end
             end
     | Gt => match splitMember' k r with
               | (lt, z, gt) => match link kx x l lt with
                                              | lt' => (lt', z, gt)
                                            end
             end
     | Eq => (l, true, r)
    end
 end.

Lemma splitMember_splitMember' : forall x s, splitMember x s  = splitMember' x s.
Proof.
  intros.
  unfold splitMember.
  induction s.
  * simpl.
    rewrite <- IHs1. clear IHs1.
    rewrite <- IHs2. clear IHs2.
    destruct (compare x k).
    + reflexivity.
    + destruct (_ x s2); reflexivity.
    + destruct (_ x s3); reflexivity.
  * reflexivity.
Qed.

Lemma splitMember_Desc:
  forall x s lb ub,
  Bounded s lb ub ->
  forall (P : Map e a * bool * Map e a -> Prop),
  (forall s1 b s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    b = isSome (sem s x) ->
    (forall i, sem s i =
          (if i == x then sem s i
           else  (sem s1 i ||| sem s2 i))) ->
    P (s1, b, s2)) ->
  P (splitMember x s) : Prop.
Proof.
  intros ?? ?? HB.
  rewrite splitMember_splitMember'.
  induction HB.
  Ltac solveThis ::= intros X HX; apply HX; clear X HX; [solve_Bounded|solve_Bounded|try reflexivity |f_solver].
  * solveThis.
  * simpl.
    destruct (compare x x0) eqn:?.
    + solveThis.
      replace (x == x0) with true by order_Bounds.
      simpl_options.
      reflexivity.
    + apply IHHB1.
      intros s1_2 b s1_3 HB1_2 HB1_3 Hb Hsems1.
      clear IHHB1 IHHB2.
      applyDesc link_Desc.
      solveThis.
      replace (x == x0) with false by order_Bounds.
      rewrite (sem_outside_below HB2) by order_Bounds.
      simpl_options. assumption.
    + apply IHHB2.
      intros s2_2 b s2_3 HB2_2 HB2_3 Hb Hsems2.
      clear IHHB1 IHHB2.
      applyDesc link_Desc.
      solveThis.
      replace (x == x0) with false by order_Bounds.
      rewrite (sem_outside_above HB1) by order_Bounds.
      simpl_options. assumption.
Qed.

(** ** Verification of [intersection] *)

Lemma intersection_Desc:
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (intersection s1 s2) lb ub
        (fun i => sem s1 i &&& sem s2 i).
Proof.
  intros ???? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  - simpl. solve_Desc.
  - simpl.
    destruct s3 eqn:Hs3.
    + rewrite <- Hs3 in *.
      clear Hs3 s e0 a0 m1 m2.
      eapply splitMember_Desc;
        only 1: eassumption.
      intros s4' b s5' HB1 HB2 Hb Hi.
      applyDesc IHHB1_1.
      applyDesc IHHB1_2.
      destruct b.
      * destruct_ptrEq.
        -- solve_Desc.
        -- applyDesc link_Desc.
           solve_Desc.
      * applyDesc link2_Desc.
        solve_Desc.
    + solve_Desc.
Qed.

(** ** Verification of [difference] *)

(** A wart: Because we are in a section that fixes [a], 
we get this proof only for invocations of [difference] where
boths maps have the same element type. This does not
affect the proof, but requires some Coq proof structure engineering
to fix. *)

Lemma difference_destruct :
  forall (P : Map e a -> Prop),
  forall s1 s2,
  (s1 = Tip -> P Tip) ->
  (s2 = Tip -> P s1) ->
  (forall sz2 x vx l2 r2, (s2 = Bin sz2 x vx l2 r2) -> 
    P (
      match split x s1 with
      | pair l1 r1 =>
      match difference r1 r2 with
      | r1r2 =>
      match difference l1 l2 with
      | l1l2 => if size l1l2 + size r1r2 == size s1
                then s1 else link2 l1l2 r1r2
      end end end)) ->
  P (@difference e a a _ _ s1 s2).
Proof.
  intros P s1 s2 HTipL HTipR HBins.
  destruct s1, s2; simpl difference;
  try destruct s1_1, s1_2;
  try destruct s2_1, s2_2;
  first [ eapply HBins; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed.

Lemma difference_Desc :
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  forall (P : Map e a -> Prop),
  (forall s,
    Bounded s lb ub ->
    size s <= size s1 ->
    (size s = size s1 -> forall i, sem s i = sem s1 i) ->
    (forall i, sem s i = diffo (sem s1 i) (sem s2 i)) ->
    P s) ->
  P (difference s1 s2).
Proof.
  intros s1 s2 lb ub Hb1 Hb2.
  revert s1 Hb1. induction Hb2; intros sl Hb1; apply hide.
  Ltac showP := apply unhide; intros X HX; apply HX; clear X HX; only 3: intro.
  - simpl.
    destruct sl; (showP; [assumption | reflexivity | reflexivity | f_solver]).
  - apply difference_destruct; intros; subst.
    + (showP; [assumption | reflexivity | reflexivity | f_solver]).
    + (showP; [assumption | reflexivity | reflexivity | f_solver]). 
    + eapply split_Desc; try eassumption. 
      intros sl1 sl2 HBsl1 HBsl2 Hsz Hsem. inversion H3; subst; clear H3.
      eapply IHHb2_1. solve_Bounded. intros sil ????. clear IHHb2_1.
      eapply IHHb2_2. solve_Bounded. intros sir ????. clear IHHb2_2.
      destruct (_ == _) eqn:Hcomp.
      * showP; [assumption | reflexivity | reflexivity | ].
        assert (size sl1 + size sl2 <= size sl) by (destruct (sem sl x0); simpl in *; lia).
        change (size sil + size sir =? size sl = true) in Hcomp.
        rewrite Z.eqb_eq in Hcomp.
        lapply H4; [intro; subst; clear H4|lia].
        lapply H8; [intro; subst; clear H8|lia].
        assert (sem sl x0 = None) by (destruct (sem sl x0); simpl in *; try reflexivity; lia).
        f_solver. (* TODO: More stuff that [f_solver] should do *)
      * applyDesc link2_Desc.
        showP.
        -- assumption.
        -- destruct (sem sl x0); simpl in *; lia.
        -- assert (sem sl x0 = None) by (destruct (sem sl x0); simpl in *; try reflexivity; lia).
           rewrite H11 in Hsz.
           simpl in Hsz.
           lapply H4; [intro; subst|lia].
           lapply H8; [intro; subst|lia].
           clear H4 H8.
           f_solver.
        -- f_solver.
Qed.

(*START - Following Set for now *)
(* no disjoint*)

(* Note: a function to get the second value in a list of tuples. Later lemma prove that this
is equivalent to folding over the second element explcitly *)
Fixpoint second_value_in_tuple_list {a : Type} {b : Type} (l : list (a * b)) : list b :=
  match l with
  | nil => nil
  | (x, y) :: tl => y :: second_value_in_tuple_list tl
  end.
(*A useful lemma that is used in the next two properties, concerning turning a map into a list*)
Lemma foldr_with_assoc:
  forall (m : Map e a) (l : list a),
    foldr cons l m = foldr cons nil m ++ l. 
Proof.
  intros. generalize dependent l.  induction m; intros.
  - simpl. rewrite IHm2. rewrite  IHm1. rewrite IHm1 with(l:=(a0 :: foldr cons nil m2)). 
    rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.
(*States that folding two maps into lists can be done by folding each separately and appending or
folding them together, using one as the base*)
Lemma foldr_with_cons:
  forall (m1 : Map e a)(m2 : Map e a),
    foldr cons (foldr cons nil m2) m1 = foldr cons nil m1 ++  foldr cons nil m2.
  Proof.
  intros. generalize dependent m2. induction m1; intros.
  - simpl. rewrite IHm1_2. rewrite foldr_with_assoc. rewrite foldr_with_assoc with(l:=(a0 :: foldr cons nil m1_2)).
    rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.
(*Generalized lemma used to prove next property*)
Lemma foldrWithKey_elem_equivalence_help:
  forall (m : Map e a) (l : list a),
  foldrWithKey(fun a b xs => b :: xs) l m = app (elems m) l.
Proof.
  intros. generalize dependent l. unfold elems. induction m; intros.
  - simpl. rewrite IHm2. rewrite IHm1.  simpl. rewrite foldr_with_assoc with(l:=(a0 :: foldr cons nil m2)).
    rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.
(*States that the elems (value list) of a map is equivalent to using foldrWithKey with
the function (fun a b xs => b :: xs). Since elems is defined using foldR, this proves an 
equivalence of foldR and foldrWithKey*)
Lemma foldrWithKey_elem_equivalence:
  forall (m : Map e a),
  foldrWithKey(fun a b xs => b :: xs) nil m = elems m.
Proof.
  intros. rewrite <- app_nil_r.  apply foldrWithKey_elem_equivalence_help. Qed.

(*This relates foldr and foldrWithKey in a more general way - that using foldr with a function f
is the same as foldrWithKey when f is applied only to the value*)
Lemma foldr_foldrWithKey_equiv:
  forall {k : Type}(m : Map e a) (f : a -> k -> k)( n : k),
  foldr f n m = foldrWithKey (fun a b xs => f b xs) n m.
Proof.
  intros. generalize dependent n. induction m; intros.
  - simpl. rewrite IHm2. rewrite IHm1. reflexivity.
  - simpl. reflexivity.
Qed.

(*This relates foldr and the fold_right function on lists, showing that they can be performed
in any order*)
Lemma fold_right_toList_go:
  forall {k : Type} (f: a -> k -> k) (n : k) (m: Map e a) (xs : list a),
  fold_right f n (foldr cons xs m) = foldr f (fold_right f n xs) m.  
Proof.
  intros. generalize dependent xs. induction m; intros.
  - simpl. rewrite IHm1. simpl. rewrite IHm2. reflexivity.
  - simpl. reflexivity.
Qed.

(*We want to relate foldr with toList. Since toList produces a list of (k, v) tuples, an analagous
theorem as foldr_spec in SetProofs is not actually true. But we can use elems instead.*)
Lemma foldr_spec:
  forall {k} (f: a-> k -> k) (n : k) (m : Map e a),
  foldr f n m = fold_right f n (elems m).
Proof.
  intros. unfold elems. erewrite fold_right_toList_go. simpl. reflexivity.
Qed.
(*Verificiation of foldr'*)
Lemma foldr'_spec:
  forall {k : Type} (f : a -> k -> k) (n : k) (m : Map e a),
  foldr' f n m = foldr f n m.
Proof. reflexivity. Qed.

(*A more general version of the original foldrWithKey, takes in arbitrary function
and can be used with toList, keys, and elems*)
Lemma foldrWithKey_multiple_folds :
  forall {k : Type} (m : Map e a) (l : list k) (f : e -> a -> k),
  foldrWithKey (fun a b xs => f a b :: xs) l m = foldrWithKey (fun a b xs => f a b :: xs) nil m ++ l.
Proof.
  intros. generalize dependent l. induction m; intros.
  - simpl. rewrite IHm1. rewrite IHm2.   
    rewrite IHm1 with(l:=(f k0 a0 :: foldrWithKey (fun (a1 : e) (b : a) (xs : list k) => f a1 b :: xs) nil m2)).
    rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.

(*This lemma, used in proving elems_to_list_second_lemma, is the foldrWithKey analogue of
foldr_with_assoc*)
Lemma foldrWithKey_toList :
  forall (m : Map e a) (l : list (e *a)),
  foldrWithKey (fun a b xs => (a,b) :: xs) l m = foldrWithKey (fun a b xs => (a,b) :: xs) nil m ++ l.
Proof.
  intros. apply foldrWithKey_multiple_folds. Qed.

(*This lemma states that we can retrieve the second value from two appended lists either before
or after appending them, with the same result*)
Lemma second_value_app:
  forall (k : Type)(s : Type) (l1 : list (s * k) )(l2 : list (s * k) ),
    second_value_in_tuple_list (l1 ++ l2) = second_value_in_tuple_list l1 ++ 
    second_value_in_tuple_list l2.
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. destruct a0. reflexivity.
Qed. 

(*This short lemma states that we can disregard information about the head tuple of a list when
retrieving its second element.*)
Lemma second_value_cons:
  forall (k : Type) (s : Type) (t1: k) (t2 : s) (l : list (k * s)),
    second_value_in_tuple_list ((t1, t2) :: l) = t2 :: second_value_in_tuple_list l.
Proof. 
  intros. simpl. reflexivity.
Qed.

(*This lemma proves the equivalence between the two ways we can get the values of the map. Either
we can foldrWithKey and explicitly retrive the second element (as in elem), or we can get the list
of tuples from toList and then retrieve each of the second elements.*)
Lemma elems_toList_second_lemma:
  forall (m : Map e a) (l : list a), 
    second_value_in_tuple_list (toList m) ++ l = foldrWithKey(fun a b xs => b :: xs) l m.
Proof.
  intros. generalize dependent l. induction m; intros.
  - simpl. unfold toList. unfold toAscList. simpl. unfold toList in *. unfold toAscList in *.
    rewrite <- IHm2. rewrite <- IHm1. rewrite foldrWithKey_toList. 
    rewrite second_value_app. rewrite -> second_value_cons. rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.

(*A simple corollary of the previous lemma, it states more explicitly the relationship between elems
and toList - we can get elems by taking the second elemen in each tuple in toList*)
Corollary elems_toList_second: 
  forall (m : Map e a),
    second_value_in_tuple_list (toList m) = elems m.
Proof.
  intros. unfold elems. rewrite foldr_foldrWithKey_equiv. rewrite <- (elems_toList_second_lemma _ nil).
  rewrite app_nil_r. reflexivity.
Qed.

Lemma elems_Bin:
  forall sz key value (m1 m2 : Map e a),
  elems (Bin sz key value m1 m2) = elems m1 ++ (value :: nil) ++ elems m2.
Proof.
  intros. 
  unfold elems at 1. simpl. rewrite foldr_with_assoc with(l:=(value :: foldr cons nil m2)).
  reflexivity.
Qed.

(*The following theorems are the axioms from ContainerAxioms*)

(*A helpful lemma that allows us to use reflexivity to prove that x == x*)
Lemma eq_coq_implies_haskell : forall {x : Type} { y : Type} `{Eq_ x} `{Eq_ y} `{EqLaws x} `{EqLaws y} x0 y0,
   x0 = y0 -> _GHC.Base.==_  x0 y0 = true .
Proof.
  intros. subst. apply Lemmas.Eq_eq_refl. 
Qed. 

(*Simpler definition of lookup*)
Fixpoint lookup' (key : e) (map : Map e a) : option a :=
  match map with
  | Tip => None
  | Bin sz k1 v1 lt rt => match compare key k1 with
                          | Eq => Some v1 
                          | Lt => lookup' key lt 
                          | Gt => lookup' key rt
                          end
 end.  

(*Prove the two definitions are equivalent*)
Lemma lookup_lookup'_equiv : forall  (key : e) (map : Map e a),
    lookup key map = lookup' key map.
Proof.
  intros. induction map.
  - simpl. destruct (compare key k); try (reflexivity); assumption.
  - simpl. reflexivity.
Qed.  

(*This lemma says that if two keys are equal, then the result of member is the same when either is called*)
Lemma member_eq: forall {a : Type} (n : e) (n' : e) (m : Map e a),
  n == n' = true ->
  member n m = member n' m.
Proof.
  intros. induction m.
   - simpl. destruct (compare n k) eqn : E.
    + rewrite Ord_compare_Eq in E.  
      apply Lemmas.Eq_trans_l  with(z:=k) in H.
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Eq in H.
      rewrite H. reflexivity.
    + rewrite Ord_compare_Lt in E. 
      apply Lemmas.Eq_le_r with(z:=k) in H. rewrite E in H. 
      symmetry in H. rewrite <- Ord_compare_Lt in H. 
      rewrite H. assumption.
    + rewrite Ord_compare_Gt in E. apply Lemmas.Eq_le_l with (z:=k) in H.
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Gt in H.
      rewrite H. assumption.
  - simpl. reflexivity.
Qed.

(*If we insert a (key, value) in a map, then looking up the key gives the value*)
Lemma lookup_insert : forall `{Eq_ a} `{EqLaws a} (key: e) (value : a) (map : Map e a) lb ub,
  Bounded map lb ub ->
  isLB lb key = true ->
  isUB ub key = true ->
  lookup' key (insert' key value map)  == Some value = true.
Proof.
  intros. pose proof (insert_Desc key value map lb ub) as H5. eapply H5 in H2. 
  unfold Desc in H2. destruct H2 with(P:= fun (map1 : Map e a) => lookup' key map1 == Some value = true).
  - intros. 
  assert (sem s key = (if _GHC.Base.==_ key key then Some value else None) ||| sem map key). { apply H8. }
  rewrite eq_coq_implies_haskell in H9. simpl in H9. eapply lookup_spec in H6. 
  rewrite <- H6 in H9. apply eq_coq_implies_haskell. rewrite <- lookup_lookup'_equiv. assumption.
  reflexivity.
  - rewrite insert_insert'. reflexivity.
  - assumption.
  - assumption.
Qed.

(*If we lookup a key key1, the result is the same regardless of whether or not we have inserted key2 
(a different key than key1)*)
Lemma lookup_insert_neq : forall `{Eq_ a} `{EqLaws a} (key1: e) (key2: e) (value : a) (map : Map e a) lb ub,
  Bounded map lb ub ->
  isLB lb key2 = true ->
  isUB ub key2 = true ->
  key1 == key2 = false -> 
  lookup' key1 (insert' key2 value map) = lookup' key1 map.
Proof.
  intros. pose proof (insert_Desc key2 value map lb ub) as H6. assert (A := H2). eapply H6 in H2. 
  unfold Desc in H2. destruct H2 with(P:= fun (map1 : Map e a) => lookup' key1 map1 = lookup' key1 map).
  - intros. assert (sem s key1 = (if _GHC.Base.==_ key1 key2 then Some value else None) ||| sem map key1).
    { apply H9. } rewrite H5 in H10. simpl in H10. 
  eapply lookup_spec in H7. rewrite <- H7 in H10. eapply lookup_spec in A. rewrite <- H10 in A.
  rewrite <- lookup_lookup'_equiv. rewrite <- A. rewrite lookup_lookup'_equiv. reflexivity.
  - rewrite insert_insert'. reflexivity.
  - assumption.
  - assumption.
Qed.

(*Similar to lookup_spec (but a bit more complicated because of the use of Props rather than booleans),
this states that a key is in a map iff there exists some value such that sem key map returns that value*)
Lemma member_spec:
 forall {s lb ub i}, Bounded s lb ub -> member i s = true <-> exists v, sem s i = Some v.
Proof.
  intros. induction H.
  - simpl. split. intros. discriminate H. intros. destruct H. discriminate H. 
  - subst. simpl. destruct (compare i x) eqn: ?; split; intros.
    + replace (i==x) with true by order_Bounds.
      rewrite (sem_outside_above H) by order_Bounds.
      simpl. exists v. reflexivity.
    + reflexivity.
    + replace (i==x) with false by order_Bounds.
      rewrite (sem_outside_below H0) by order_Bounds.
      simpl_options. apply IHBounded1 in H3. destruct H3. exists x0. assumption.
    + assert (sem s2 i = None). { eapply sem_outside_below. apply H0. unfold isLB.
      order_Bounds. }
      rewrite H5 in H3. assert (i == x = false). { rewrite compare_Lt in Heqc.
      apply lt_not_eq. assumption. } rewrite H6 in H3. simpl in H3. simpl_options. 
      apply IHBounded1. destruct H3. exists x0. assumption. 
    + replace (i==x) with false by order_Bounds.
      rewrite (sem_outside_above H) by order_Bounds.
      simpl. apply IHBounded2 in H3. destruct H3. exists x0. assumption.
    + assert (sem s1 i = None). { eapply sem_outside_above. apply H. order_Bounds. }
      rewrite H5 in H3. rewrite compare_Gt in Heqc. apply gt_not_eq in Heqc. rewrite Heqc in H3.
      simpl_options. destruct H3. apply IHBounded2. exists x0. assumption.
Qed.


(*Probably in the standard library, but needed in the next proof*)
Lemma contrapositive : forall (P : Prop) (Q: Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. intro. apply H in H1. contradiction.
Qed. 

(*States that if we check for key1 in the map in which we have inserted key2, then either
key1 was already in the map, or key1 == key2*)
Lemma member_insert: forall key1 key2 value map lb ub,
  Bounded map lb ub ->
  isLB lb key2 = true ->
  isUB ub key2 = true ->
  member key1 (insert' key2 value map) = (key1 == key2) || member key1 map.
Proof.
  intros. pose proof (insert_Desc key2 value map lb ub) as H5. assert (A := H). eapply H5 in H.
  unfold Desc in H. 
  destruct H with(P:= fun (map1 : Map e a) => member key1 map1 = (key1 == key2) || member key1 map).
  - intros. assert(sem s key1 = (if _GHC.Base.==_ key1 key2 then Some value else None) ||| sem map key1).
    { apply H4. } destruct (key1 == key2) eqn : ?. simpl in H6. 
    eapply member_spec in H2. destruct H2. assert (member key1 s = true). { apply H7. exists value.
    assumption. } rewrite H8. simpl. reflexivity. 
    eapply member_spec in H2. destruct H2. simpl in H6. destruct (sem s key1) eqn : E.
    + assert (member key1 s = true). { apply H7. exists a0. assumption. } 
      eapply member_spec in A. destruct A. assert (member key1 map =true). {
      apply H10. exists a0. symmetry in H6. assumption. }
      rewrite H11. simpl. assumption.
    + simpl. eapply member_spec in A. destruct A. assert (member key1 s = false). {
      apply contrapositive in H2. destruct (member key1 s)  eqn : ?. contradiction.
      reflexivity. intro. destruct H10. rewrite H10 in E. discriminate E. }
      assert (member key1 map = false). { apply contrapositive in H8. 
      destruct (member key1 map) eqn : ?. rewrite Heqb0 in H8. contradiction.
      reflexivity. intro. destruct H11. rewrite H11 in H6. discriminate H6. }
      rewrite H10. rewrite H11. reflexivity.
  - rewrite insert_insert'. reflexivity.
  - assumption.
  - assumption.
Qed.

(*If we lookup a key that is deleted, we should get None*)
Lemma delete_eq : forall key map lb ub,
  Bounded map lb ub ->
  lookup key (delete key map) = None.
Proof.
  intros. pose proof (delete_Desc key map lb ub) as H2. eapply H2 in H. unfold Desc in H.
  destruct H with(P:= fun (map1 : Map e a) => lookup key map1 = None).
  - intros. eapply lookup_spec in H0.
    assert (sem s key = (if _GHC.Base.==_ key key then None else sem map key)). { apply H3. }
    rewrite eq_coq_implies_haskell in H4. rewrite H4 in H0. assumption. reflexivity.
  - reflexivity. 
Qed.

(*If we delete a key key2 and then lookup a different key key1, then it should be the same regardless of
whether or not key2 was deleted.*)
Lemma delete_neq : forall key1 key2 map lb ub,
  Bounded map lb ub ->
  key1 == key2 = false ->
  lookup key1 (delete key2 map) = lookup key1 map.
Proof.
  intros. pose proof(delete_Desc key2 map lb ub) as H1. assert(A:= H). eapply H1 in H.
  unfold Desc in H. destruct H with(P:= fun (map1 : Map e a) => lookup key1 map1 = lookup key1 map).
  - intros. assert (sem s key1 = (if _GHC.Base.==_ key1 key2 then None else sem map key1)). { apply H4. }
    rewrite H0 in H5. eapply lookup_spec in H2. eapply lookup_spec in A. rewrite H5 in H2.
    rewrite <- H2 in A. symmetry. assumption.
  - reflexivity.
Qed. 

(*Same as above but for member*)
Lemma member_delete_neq: forall key1 key2 map lb ub,
  Bounded map lb ub ->
  key1 == key2 = false ->
  member key2 (delete key1 map) = member key2 map.
Proof.
  intros. pose proof(delete_Desc key1 map lb ub) as H1. assert(A:=H). eapply H1 in H.
  unfold Desc in H. destruct H with(P:= fun(map1 : Map e a) => member key2 map1 = member key2 map).
  - intros. assert (sem s key2 = (if _GHC.Base.==_ key2 key1 then None else sem map key2)). { apply H4. }
    rewrite Lemmas.Eq_neq_sym in H5. eapply member_spec in H2. eapply member_spec in A.
    destruct (sem s key2)  eqn : ?.
    + destruct A. assert (member key2 map = true). { apply H7. exists a0. symmetry. assumption. }
      destruct H2. assert (member key2 s = true). { apply H9. exists a0. assumption. }
      rewrite H8. rewrite H10. reflexivity.
    + destruct A. destruct H2. apply contrapositive in H6. apply contrapositive in H2.
      destruct (member key2 s) eqn : ?. contradiction. destruct (member key2 map) eqn : ?.
      contradiction. reflexivity. intro. destruct H9. rewrite H9 in Heqo. discriminate Heqo.
      intro. destruct H9. rewrite H9 in H5. discriminate H5.
    + assumption.
 - reflexivity.
Qed.

(*States that if a key is not in the map, then looking it up will give None, and vice versa.
Note, in ContainerAxioms, this is defined with = rather than <->, but that introduced some
difficulty in the proof *)
Lemma non_member_lookup :
  forall key map lb ub,
  Bounded map lb ub ->
  (member key map = false) <-> (lookup key map = None).
Proof.
  intros. assert(A:=H). eapply member_spec in H.  destruct (member key map) eqn : E.
  - destruct H. apply H in E. destruct E. eapply lookup_spec in A. rewrite H1 in A.
    rewrite A.  split; intros; discriminate H2. 
  - split; intros. destruct H. apply contrapositive in H1. destruct (lookup key map) eqn :?.
    + unfold not in H1. destruct H1. exists a0. eapply lookup_spec in A.
      rewrite Heqo in A. symmetry. assumption.
    + reflexivity. 
    + intro. rewrite H2 in E. discriminate E.
    + reflexivity.
Qed.

(*If two keys are equal (according to the Eq typeclass), then their values in 
a map are equal*)
Lemma lookup_eq : forall k k' (m : Map e a),
    k == k' = true ->
    lookup k m = lookup k' m.
Proof.
  intros. induction m.
  - simpl. destruct (compare k k0) eqn : E.
    + rewrite Ord_compare_Eq in E. apply Lemmas.Eq_trans_l with(z:=k0) in H .
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Eq in H.
      rewrite H. reflexivity.
    + rewrite Ord_compare_Lt in E. apply Lemmas.Eq_le_r with (z:= k0) in H.
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Lt in H.
      rewrite H. assumption.
    + rewrite Ord_compare_Gt in E. apply Lemmas.Eq_le_l with (z:=k0) in H.
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Gt in H.
      rewrite H. assumption.
  - simpl. reflexivity.
Qed.

(*This follows almost immediately from member_spec*)
Lemma member_lookup : 
  forall key map lb ub,
  Bounded map lb ub -> 
  (member key map = true) <-> (exists value, lookup key map = Some value).
Proof.
  intros. assert(A:=H). eapply member_spec in A. eapply lookup_spec in H.
  rewrite <- H in A. apply A.
Qed. 

(*verification of null*)
Lemma null_empty: 
    @null e a empty = true.
Proof.
  unfold null. simpl. reflexivity.
Qed. 

(*Second section of ContainerAxioms*)

(*A key is a member of the union of two maps whenever it is a member of at least one of the maps*)
Lemma member_union :
  forall key map1 map2 lb ub,
  Bounded map1 lb ub ->
  Bounded map2 lb ub ->
  member key (union map1 map2) = member key map2 || member key map1.
Proof.
  intros. pose proof(union_Desc map1 map2 lb ub) as H1. assert (A:=H).
  eapply H1 in H. unfold Desc' in H. 
  destruct H with(P:= fun (m : Map e a) => member key m = member key map2 || member key map1).
  - intros. assert (sem s key = sem map1 key ||| sem map2 key). { apply H4. }
    eapply member_spec in H2. eapply member_spec in A.
    unfold oro in H5. destruct (sem map1 key) eqn : ?.
    + assert (member key s = true). { apply H2. exists a0. assumption. }
      assert (member key map1 = true). { apply A. exists a0. assumption. }
      rewrite H6. rewrite H7. symmetry. rewrite orb_true_iff. right. reflexivity.
    + destruct A. destruct H2. eapply member_spec in H0. destruct H0.
      destruct (sem s key) eqn : ?.
      * assert (member key s = true). { apply H8. exists a0. reflexivity. }
        assert (member key map2 = true). { apply H9. exists a0. symmetry. assumption. }
        rewrite H10. rewrite H11. simpl. reflexivity.
      * apply  contrapositive in H6. apply contrapositive in H2. apply contrapositive in H0.
        destruct (member key s). contradiction. destruct (member key map1). contradiction.
        destruct (member key map2). contradiction. simpl. reflexivity.
        intro. destruct H10. rewrite H10 in H5. discriminate H5.
        intro. destruct H10. discriminate H10.
        intro. destruct H10. rewrite H10 in Heqo. discriminate Heqo.
  - reflexivity.
  - assumption.
Qed. 

(*The union of a map with the empty map (in both directions) is itself*)
Lemma union_nil_l : forall map ub lb,
  Bounded map ub lb ->
  union empty map = map.
Proof.
  intros.  induction H.
  - reflexivity.
  - simpl. destruct s1 eqn : ?. reflexivity.
    destruct s2 eqn : ?. reflexivity.
    unfold insertR. unfold singleton. simpl in H3.
    rewrite H3. reflexivity.
Qed.

Lemma union_nil_r : forall map ub lb,
  Bounded map ub lb ->
  union map empty = map.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. destruct s1. reflexivity. destruct s2. reflexivity. reflexivity.
Qed.

(*Verification of empty - a map is empty iff for all keys, sem map key gives None*)
Lemma empty_Spec: forall map lb ub,
  Bounded map lb ub ->
  (forall key, sem map key = None) <-> map = empty.
Proof.
  intros. split.
  - intros. induction H.
    + unfold empty. reflexivity. 
    + assert (sem (Bin sz x v s1 s2) x = Some v). { simpl.
      assert (sem s1 x = None). { eapply sem_outside_above. apply H.
      order_Bounds. }
      rewrite H6. simpl. rewrite Lemmas.Eq_eq_refl. simpl. reflexivity. }
      assert (sem (Bin sz x v s1 s2) x = None). { apply H0. }
      rewrite H7 in H6. discriminate H6.
  - intros. rewrite H0. simpl. reflexivity.
Qed.

(*The difference between a map and itself is the empty map*)
Lemma difference_self: forall map lb ub,
  Bounded map lb ub ->
  difference map map = empty.
Proof.
  intros. pose proof(difference_Desc map map lb ub) as H1. assert(A:=H). 
  eapply H1 with(P:= fun(map1 : Map e a) => map1 = empty) in A .
  - assumption.
  - assumption.
  - intros. assert ( forall i, sem s i = None). {
    intros. assert (sem s i = diffo (sem map i) (sem map i)). { apply H4. }
    unfold diffo in H5. destruct (sem map i) eqn : ?.
    assumption. assumption. }
    rewrite empty_Spec in H5. assumption. apply H0.
Qed.

(*The difference of a map with the empty map is itself*)
Lemma difference_nil_r: forall `{Eq_ a} `{EqLaws a} (B : Type) map lb ub,
  Bounded map lb ub ->
  difference map (@empty e B) = map.
Proof.
  intros. inversion H2.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*The difference of the empty map with any map is empty*)
Lemma difference_nil_l: forall `{Eq_ a} `{EqLaws a} (B : Type) map lb ub (key : e),
  Bounded map lb ub ->
  difference (@empty e B) map = empty.
Proof.
  intros. inversion H2.
  - simpl. reflexivity.
  - simpl. unfold empty. reflexivity.
Qed.

(*Follows from sem_inside, says that if a key is in a map, it is between the bounds*)
Lemma keys_inside_bounds : forall map key lb ub,
  Bounded map lb ub ->
  member key map = true ->
  isLB lb key = true /\ isUB ub key = true .
Proof.
  intros. eapply member_spec in H0. destruct H0.
  eapply sem_inside. apply H. apply H0. apply H.
Qed.

(*If a key is in a map, the difference of the singleton map containing only that key
and the original map is empty*)
Lemma difference_Tip_member: forall map (key :e) lb ub,
  Bounded map lb ub ->
  member key map = true ->
  forall (value : a), difference (singleton key value) map = empty.
Proof.
  intros. assert (A:=H). induction H.
  - discriminate H0.
  - pose proof(difference_Desc (singleton key value) (Bin sz x v s1 s2) lb ub) as H6. 
  eapply H6 with(P:=(fun map1 => map1 = empty)). eapply BoundedBin. apply BoundedTip.
  apply BoundedTip. eapply keys_inside_bounds in H0. destruct H0.
  apply H0. apply A. eapply keys_inside_bounds in H0. destruct H0. apply H7.
  apply A. simpl. reflexivity. simpl. unfold balance_prop. simpl. omega. apply A.
  intros.  eapply member_spec in H0. destruct H0.
  assert (forall i : e, sem s i = None). {
  intros i. assert (sem s i = diffo (sem (singleton key value) i) (sem (Bin sz x v s1 s2) i)). {
  apply H10. } destruct (i == key) eqn : ?.
  + simpl in H11. rewrite Heqb in H11. simpl in H11. 
    assert (sem s1 i = sem s1 key). { apply sem_resp_eq. assumption. } 
    assert (sem s2 i = sem s2 key). { apply sem_resp_eq. assumption. } 
    assert ((i == x) = (key == x)). { eapply Lemmas.Eq_trans_l. assumption. }
    rewrite H12 in H11. rewrite H14 in H11. rewrite H13 in H11. simpl in H0.
    rewrite H0 in H11. simpl in H11. apply H11. 
  + simpl in H11. rewrite Heqb in H11. simpl in H11. unfold diffo in H11. 
    destruct (sem s1 i ||| SomeIf (_GHC.Base.==_ i x) v ||| sem s2 i) eqn : ?.
    assumption. assumption. }
    rewrite <- empty_Spec. apply H11. apply H7. apply A.
Qed.
(*A bunch of things that will help to prove equality between two maps. First, this is a function
that sees whether the given key and value are in a map. Cannot use List.elems because the Haskell
notion of equality is not strong enough*)
Fixpoint In (key : e) (value : a) (l : list (e * a)) : Prop :=
  match l with
  | nil => False
  | a :: tl => (let (x,y):= a in x == key = true /\ y = value) \/ In key value tl
  end.

(*Allows us to decompose toList*)
Lemma toList_Bin:
  forall sz key value (m1 m2 : Map e a),
  toList (Bin sz key value m1 m2) = toList m1 ++ (key, value) :: nil ++ toList m2.
Proof.
  intros.
  unfold toList at 1. unfold toAscList at 1. simpl.
  rewrite foldrWithKey_toList. reflexivity.
Qed. 

(*Helper methods for logic: probably in the standard library*)
Lemma or_assoc: forall b1 b2 b3,
  (b1 \/ b2) \/ b3 <-> b1 \/ ( b2 \/ b3).
Proof.
  intros. split; intros.
  - destruct H. destruct H. left. assumption. right. left. assumption. right.
    right. assumption.
  - destruct H. left. left. assumption. destruct H. left. right. assumption. right.
    assumption.
Qed.


Lemma false_or: forall (P : Prop),
  False \/ P <-> P.
Proof.
  intros. split; intros.
  - destruct H. destruct H. apply H.
  - right. apply H.
Qed. 

(*Key property of In for lists - if we append to 2 lists, an item is in the whole list
iff it is in one of them*)
Lemma elem_or : forall key value l1 l2,
  In key value (l1 ++ l2) <-> In key value l1 \/ In key value l2.
Proof.
  intros. generalize dependent l2. induction l1.
  - intros. simpl. split; intros.
    + right. assumption.
    + destruct H. destruct H. assumption.
  - intros. simpl. rewrite IHl1. rewrite or_assoc. apply iff_refl.
Qed.

(*plan for equality
1. a (k,v) pair is in toList iff sem m key = Some value (DONE)
2. (corollary) if 2 maps have same sem, then their toList have the same elements
3. toList is sorted (DONE)
4. sorted lists are unique
5  therefore, these are the same list*)

(*This says that sem m key returns a Value iff that key, value pair appears in the 
resulting toList of the map*)
Lemma toList_sem :
  forall  `{EqLaws a}  m lb ub, Bounded m lb ub ->
  forall key value, sem m key = Some value <-> In key value (toList m).
Proof.
  intros. generalize dependent value. induction H1.
  - simpl. intros. split; intros. discriminate H1. destruct H1.
  - intros. simpl. rewrite toList_Bin. rewrite elem_or. 
    assert (((x, v) :: nil ++ toList s2) = (((x, v) :: nil) ++ toList s2)).
    simpl. reflexivity. rewrite H5. rewrite elem_or. split; intros.
      + destruct (sem s1 key) eqn : ?; simpl in H6.
      * apply IHBounded1 in H6. left. apply H6. 
      * destruct (key == x) eqn : ?; simpl in H6.
        { right. left. simpl. left. apply Eq_Symmetric in Heqb.
          split. apply Heqb. inversion H6. reflexivity. }
        { apply IHBounded2 in H6. right. right. assumption. }
     + destruct H6.
      * apply IHBounded1 in H6. rewrite H6. simpl. reflexivity.
      * destruct H6. simpl in H6. destruct H6. destruct H6.
        assert (sem s1 key = None). { eapply sem_outside_above.
        apply H1_. order_Bounds. }
        rewrite H8. simpl. apply Eq_Symmetric in H6. rewrite H6. simpl.
        rewrite H7. reflexivity. destruct H6. apply IHBounded2 in H6.
        assert (H1_1:=H1_0). eapply sem_inside in H1_0. destruct H1_0.
        assert (sem s1 key = None). { eapply sem_outside_above. apply H1_.
        assert (isLB (Some x) key = true). { apply H7. }
        order_Bounds. }
        assert (key == x = false). { order_Bounds. }
        rewrite H9. rewrite H10. simpl. assumption. apply H6.
Qed.

(** ** Verification of [toList] *)

(*The next two lemmas say that every key in toList m is between the bounds of the map*)
Lemma toList_lb : forall m lb ub,
  Bounded m lb ub ->
  Forall (fun (i : e * a) => let (x, _) := i in isLB lb x = true) (toList m).
Proof.
  intros. induction H.
  - apply Forall_nil.
  - rewrite toList_Bin. rewrite Forall_forall in *.
    intros. simpl in H5. rewrite in_app_iff in *.
    destruct H5.
    + apply IHBounded1. assumption.
    +  simpl in H5.  destruct H5. 
      *  subst.  assumption. 
      * apply IHBounded2 in H5. simpl in H5. rename x0 into x2. 
        destruct x2. order_Bounds.
Qed.

Lemma toList_ub : forall m lb ub,
  Bounded m lb ub ->
  Forall (fun (i : e * a) => let (x, _) := i in isUB ub x = true) (toList m).
Proof.
  intros. induction H.
  - apply Forall_nil.
  - rewrite toList_Bin. rewrite Forall_forall in *. intros.
    simpl in H5. rewrite in_app_iff in *. destruct H5.
    + apply IHBounded1 in H5. destruct x0. order_Bounds.
    + simpl in H5. destruct H5. subst. assumption. apply IHBounded2. assumption.
Qed. 

(*The list of the empty tree is empty*)
Lemma toList_Tip: toList (@Tip e a) = nil.
Proof. reflexivity. Qed.

(*The list contains the left subtree, then the current value, then the right subtree
(crucial in showing that the list is sorted)*)
Lemma toList_bin:
  forall key value n (m1 m2 : Map e a),
  toList (Bin n key value m1 m2) = toList m1 ++ ((key, value) :: nil) ++ toList m2.
Proof. intros. apply toList_Bin. Qed.

(*The next two lemmas prove that the list from toList is in the same order even if we balance the tree. The
proofs are very similar to setProofs, only 1 more case at the end*)
Lemma toList_balanceR :
  forall x y m1 m2 lb ub,
  Bounded m1 lb (Some x) ->
  Bounded m2 (Some x) ub ->
  balance_prop (size m1) (size m2) \/
  balance_prop_inserted (size m2 - 1) (size m1) /\ (1 <= size m2)%Z  \/
  balance_prop (size m1 + 1) (size m2) ->
  toList (balanceR x y m1 m2) = toList m1 ++ ((x,y) :: nil) ++ toList m2.
Proof.
  intros.
  unfold balanceR.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: rewrite ?toList_Bin, <- ?app_assoc; try reflexivity.
  simpl. rewrite <- app_assoc. assert (((x2, v1) :: toList s5) ++ (x1, v0) :: toList s0 ++ (x3, v2) :: toList s6
  = (x2, v1) :: toList s5 ++ (x1, v0) :: toList s0 ++ (x3, v2) :: toList s6). simpl. reflexivity.
  rewrite H20. reflexivity.
Qed.

Lemma toList_balanceL:
  forall x y m1 m2 lb ub,
  Bounded m1 lb (Some x) ->
  Bounded m2 (Some x) ub  ->
  balance_prop (size m1) (size m2) \/
  balance_prop_inserted (size m1 - 1) (size m2) /\ (1 <= size m1)%Z \/
  balance_prop (size m1) (size m2 + 1) ->
  toList (balanceL x y m1 m2) = toList m1 ++ ((x, y) :: nil) ++ toList m2.
Proof.
  intros.
  unfold balanceL.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: rewrite ?toList_Bin, <- ?app_assoc; try reflexivity.
  - simpl. assert (toList s0 ++ (x3, v2) :: toList s6 ++ (x, y) :: toList s1 ++ (x0, v) :: toList s2
  = (toList s0 ++ (x3, v2) :: toList s6) ++ (x, y) :: toList s1 ++ (x0, v) :: toList s2).
    rewrite <- app_assoc. simpl. reflexivity. rewrite H20. reflexivity.
  - simpl. assert (toList s0 ++ (x3, v2) :: toList s6 ++ (x, y) :: toList s1 ++ (x0, v) :: toList s2 =
    (toList s0 ++ (x3, v2) :: toList s6) ++ (x, y) :: toList s1 ++ (x0, v) :: toList s2). 
    rewrite <- app_assoc. simpl. reflexivity. rewrite H20. reflexivity.
Qed.

(*If we insertMax into a tree, that value is at the end of the list*)
Lemma toList_insertMax:
   forall x y m lb,
   Bounded m lb (Some x) ->
   toList (insertMax x y m) = toList m ++ (x,y) :: nil.
Proof.
  intros. remember (Some x) as ub'. generalize dependent x.
  induction H; intros.
  - simpl. reflexivity.
  - simpl. subst. specialize(IHBounded2 x0 eq_refl). revert IHBounded2.
    assert (isUB None x0 = true) by reflexivity. applyDesc insertMax_Desc.
    intro. erewrite toList_balanceR. rewrite IHBounded2. rewrite toList_bin.
    rewrite <- app_assoc. simpl. reflexivity. apply H. apply HB.
    solve_size.
Qed.

(*If we insertMin into a tree, that value is at the beginning of the list*)
Lemma toList_insertMin:
   forall x y m ub,
   Bounded m (Some x) ub ->
   toList (insertMin x y m) = (x,y) :: nil ++ toList m.
Proof.
  intros. remember (Some x) as ub'. generalize dependent x.
  induction H; intros.
  - simpl. reflexivity.
  - simpl. subst. specialize(IHBounded1 x0 eq_refl). revert IHBounded1.
    assert (isLB None x0 = true) by reflexivity. applyDesc insertMin_Desc.
    intro. erewrite toList_balanceL. rewrite IHBounded1. rewrite toList_bin.
    simpl. reflexivity. apply HB. apply H0. solve_size.
Qed.

(*States that if we link 2 maps together, then the list is in the same order. These
past few lemmas together mean that when balancing the tree, the list does not change*)
Program Fixpoint toList_link (x : e) (y : a) (m1: Map e a)  (m2: Map e a)
  {measure (map_size m1 + map_size m2)} :
    forall lb ub,
    Bounded m1 lb (Some x) ->
    Bounded m2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    toList (link x y m1 m2) = toList m1 ++ (x,y) :: nil ++ toList m2 := _.
Next Obligation.
  intros.
  rewrite link_eq. 
  inversion H; subst; clear H;
  inversion H0; subst; clear H0.
  * reflexivity.
  * erewrite toList_insertMin by solve_Bounded.
    rewrite toList_Bin.
    reflexivity.
  * erewrite toList_insertMax by solve_Bounded.
    rewrite toList_Bin.
    reflexivity.
  * destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
    - erewrite toList_balanceL; only 3: solve_Precondition.
      erewrite toList_link by solve_Precondition.
      rewrite ?toList_Bin, <- ?app_assoc. reflexivity.
      applyDesc link_Desc; eassumption.
      applyDesc link_Desc; solve_size.
    - erewrite toList_balanceR; only 2: solve_Precondition.
      erewrite toList_link by solve_Precondition.
      rewrite ?toList_Bin, <- ?app_assoc. reflexivity.
      applyDesc link_Desc; eassumption.
      applyDesc link_Desc; solve_size.
    - rewrite ?toList_bin, ?toList_Bin, <- ?app_assoc.
      unfold bin. rewrite toList_bin. rewrite toList_bin.
      rewrite toList_bin. simpl. rewrite <- app_assoc. simpl.
      reflexivity. 
Qed.

(** *** Sortedness of [toList] *)

Require Import Coq.Sorting.Sorted.
Close Scope Z.

(*Maps are sorted only by keys*)
Local Definition lt : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 < e2) = true.

(*Since some StronglySorted lemmas are defined by List.In, we show that List.In -> In
The other direction does not hold because haskell equality does not imply Coq equality*)
Lemma In_List_In_equiv: forall x y l,
  List.In (x,y) l -> In x y l.
Proof.
  intros. induction l. 
  - simpl. simpl in H. apply H.
  - simpl. simpl in H. destruct H.
    + destruct a0. inversion H. left. split. apply Lemmas.Eq_eq_refl. reflexivity.
    + destruct a0. right. apply IHl. assumption.
Qed.

(* States that if two lists are sorted and all values in the first are smaller
than all values in the second, then appending the two lists gives a sorted list. *)
Lemma sorted_append:
  forall (l1 : list (e * a)) (l2 : list (e * a)) (x : e),
  StronglySorted lt l1 ->
  StronglySorted lt l2 ->
  (forall (y : e) (z : a), List.In (y, z) l1 -> (y < x) = true) ->
  (forall y z, List.In (y, z) l2 -> (x <= y) = true) ->
  StronglySorted lt (l1 ++ l2).
Proof.

  intros ??? Hsorted1 Hsorted2 Hlt Hge.
  induction Hsorted1.
  * apply Hsorted2.
  * simpl. apply SSorted_cons.
    + apply IHHsorted1.
      intros y z Hy.
      eapply Hlt.
      right. apply Hy.
    + rewrite Forall_forall.
      intros z Hz.
      rewrite in_app_iff in Hz.
      destruct Hz.
      - rewrite Forall_forall in H.
        apply H; auto.
      - destruct a0.  assert (e0 < x = true). eapply Hlt. left. reflexivity. 
        
        unfold lt. destruct z. apply Hge in H0. order e.
Qed.

(*Similar to List.elem, but does not require that a be in the Eq typeclass (because it doesn't actually
matter; the a's are not ever compared)*)
Fixpoint list_elem_tuple (x : e * a) (l : list (e * a)) :=
  match l with
  | nil => false
  | h :: t => let (a, b) := h in let (x1, x2) := x in (a == x1) || list_elem_tuple x t
  end.

(*This states that if x is a lower bound for a list and the tuple i is in the list, then x is less than i.
Note: this required a change from toList (using lt rather than < in the conclusion), though this 
is needed because there is no definition of ordering on all tuples*)
Lemma All_lt_elem:
  forall x i xs,
  Forall (lt x) xs ->
  list_elem_tuple i xs = true ->
  lt x i.
Proof.
  intros.
  induction H.
  * simpl in H0. inversion H0.
  * simpl in *. destruct x0. destruct i.
    rewrite orb_true_iff in H0.
    destruct H0.
    - unfold lt in *. destruct x. order e.
    - intuition.
Qed.

(*toList is sorted by key*)
Lemma to_List_sorted:
  forall m lb ub,
  Bounded m lb ub ->
  StronglySorted lt (toList m).
Proof.
  intros. induction H.
  - apply SSorted_nil.
  - rewrite toList_bin. eapply sorted_append. assumption.
    apply SSorted_cons. assumption. apply toList_lb in H0.
    apply H0. apply toList_ub in H.  intros. 
    rewrite Forall_forall in H.
    remember (y,z) as t. 
    apply H in H5. destruct t. inversion Heqt. rewrite <- H7. unfold isUB in H5. apply H5.
    intros. simpl in H5. destruct H5.
    + inversion H5. order e.
    + apply toList_lb in H0. 
      rewrite Forall_forall in H0. apply H0 in H5. order_Bounds.
Qed. 

(** ** Verification of [toAscList] *)

Lemma toAscList_spec: @toAscList = @toList. Proof. reflexivity. Qed.


(*TODO: PROVE LATER*)
Axiom sem_equality: forall `{Eq_ a} `{EqLaws a} map1 map2 lb ub,
  Bounded map1 lb ub ->
  Bounded map2 lb ub ->
  (forall key, sem map1 key = sem map2 key) -> map1 == map2 = true.



Lemma difference_Tip_non_member: forall `{Eq_ a} `{EqLaws a} map (key :e) lb ub,
  Bounded map lb ub ->
  isUB ub key = true ->
  isLB lb key = true ->
  member key map = false ->
  forall (value : a), difference (singleton key value) map == (singleton key value) = true.
Proof.
  intros. pose proof(difference_Desc (singleton key value) map lb ub) as H6. 
  assert(A:=H). assert (Bounded (singleton key value) lb ub). { unfold singleton.
  apply BoundedBin. apply BoundedTip. apply BoundedTip. assumption. assumption. simpl.
  reflexivity. simpl. unfold balance_prop. omega. } 
  eapply H6 with(P:=(fun map1 => map1 == singleton key value = true)). assumption.
  assumption. intros.
  simpl in H8.
  pose proof(@member_spec map lb ub key) as H12. assert(A1:=A). apply H12 in A.
  destruct A. apply contrapositive in H14. assert (sem map key = None). {
  unfold not in H14. destruct (sem map key). destruct H14. exists a0. reflexivity.
  reflexivity. }
  assert (forall i, i == key = false -> sem s i = None). {
  intros. assert (sem s i = diffo (SomeIf (_GHC.Base.==_ i key) value ||| None) (sem map i)). {
  apply H11. } rewrite H16 in H17. simpl in H17. unfold diffo in H17. destruct (sem map i); assumption.
  }
  assert (sem s key = Some value). { 
  assert (sem s key = diffo (SomeIf (_GHC.Base.==_ key key) value ||| None) (sem map key)). {
  apply H11. } rewrite Eq_Reflexive in H17. simpl in H17. rewrite H15 in H17. simpl in H17.
  assumption. }
  assert (forall i, sem s i = SomeIf (i == key) value). {
  intros. destruct (i == key) eqn : ?. { simpl. rewrite <- (sem_resp_eq s key).
  assumption. apply Eq_Symmetric. apply Heqb. }
  { simpl. apply H16 in Heqb. assumption. }
  } applyDesc singleton_Desc. assert (forall i, sem s i = sem s0 i). {
    intros. rewrite H18. rewrite Hsem. reflexivity. }
    eapply sem_equality. apply H8. apply HB. apply H19. intro. rewrite H15 in H5.
    discriminate H5. intros. apply H2.
Qed.
   
(*End of ContainerAxioms*) 


(* A few old proofs relating to keys/elems that can be rewritten to follow easily from
analogous proofs about toList
Lemma keys_bin:
  forall sz key value (m1 m2 : Map e a),
  keys (Bin sz key value m1 m2) = keys m1 ++ key :: nil ++ keys m2.
Proof.
  intros.
  unfold keys at 1.  simpl.
  rewrite foldrWithKey_multiple_folds. reflexivity.
Qed. 


Lemma elem_app:
  forall {a} `{Eq_ a} (i : a) xs ys,
  List.elem i (xs ++ ys) = List.elem i xs || List.elem i ys.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. rewrite IHxs. rewrite orb_assoc. reflexivity.
Qed.

Lemma keys_sem:
  forall m key value, sem m key = Some value -> List.elem key (keys m) = true.
Proof.
  intros.
  induction m.
  * rewrite keys_bin.
    simpl. rewrite elem_app.  rewrite orb_true_iff.
    inversion H. unfold oro in H1.
    destruct (sem m1 key) eqn : E. 
    - inversion H1; subst. left.
    apply IHm1. reflexivity.
    - destruct (SomeIf(_GHC.Base.==_ key k) a0) eqn : E1.
      + inversion H1; subst. right. unfold List.elem. 
         destruct (_GHC.Base.==_ key k) eqn : E2. 
          { simpl. reflexivity. }
          { simpl. apply IHm2. inversion E1. }
      + right. unfold List.elem.  destruct (_GHC.Base.==_ key k) eqn : E2. 
          { simpl. reflexivity. }
          { simpl. apply IHm2. assumption. }
   * simpl. simpl in H. discriminate H.
Qed.

Generalizable Variables a.
Lemma elems_sem:
  forall `{Eq_ a} (m : Map e a) lb ub, Bounded m lb ub ->
  forall key value, sem m key = Some value -> List.elem value (elems m) = true.
Proof.
  intros.
  induction H0.
  * simpl. simpl in H1. discriminate H1. 
  * rewrite keys_bin.
    simpl. rewrite elem_app. ewrite orb_true_iff.
    inversion H0. unfold oro in H7.
    destruct (sem s1 key) eqn : E. inversion H7; subst. left.
    apply IHBounded1. reflexivity.
    { destruct (SomeIf(_GHC.Base.==_ key x) v) eqn : E1.
      { inversion H7; subst. unfold SomeIf in E1. 
         destruct (_GHC.Base.==_ key x) eqn : E2.
          {  right. unfold List.elem. rewrite E2.
            simpl. reflexivity. }
        discriminate E1. }
     right. unfold List.elem. destruct (_GHC.Base.==_ key x) eqn: E2. simpl. 
     reflexivity. simpl. apply IHBounded2. assumption. }
Qed.*)

End WF.

