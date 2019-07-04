(* Where does this file belong? *)

Require Import Coq.Lists.List.

Lemma Forall_map:
  forall {a b} P (f : a -> b) xs,
  Forall P (map f xs) <-> Forall (fun x => P (f x)) xs.
Proof.
  intros.
  induction xs; simpl.
  * split; intro; constructor.
  * split; intro H; inversion_clear H; constructor; try apply IHxs; assumption.
Qed.

Lemma Forall_cons_iff:
  forall  {a} (P : a -> Prop) x xs,
  Forall P (x :: xs) <-> P x /\ Forall P xs.
Proof.
  intros.
  intuition; inversion H; intuition.
Qed.

(* The termination checker does not like recursion through [Forall], but
   through [map] is fine... oh well. *)
Definition Forall' {a} (P : a -> Prop) xs := Forall id (map P xs).

Lemma Forall'_Forall:
  forall  {a} (P : a -> Prop) xs,
  Forall' P xs <-> Forall P xs.
Proof.
  intros.
  unfold Forall'.
  unfold id.
  rewrite Forall_map.
  reflexivity.
Qed.

Theorem Forall_In_impl {A} {P : A -> Prop} (Q : A -> Prop) :
  forall l,
  (forall a, In a l -> P a -> Q a) ->
  Forall P l -> Forall Q l.
Proof.
  intros l; rewrite !Forall_forall; intros IMPL In__P x IN.
  now apply IMPL; [|apply In__P].
Qed.
