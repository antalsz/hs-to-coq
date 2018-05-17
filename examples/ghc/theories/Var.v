Require Import Id.
Require Import Core. (* For [Var] only *)

(** ** Stuff about [Var] and [Id] *)

Lemma getUnique_varUnique: 
    (Unique.getUnique : Var -> Unique.Unique) = varUnique.
Proof.
  unfold Unique.getUnique, Unique.getUnique__,Uniquable__Var,
     Core.Uniquable__Var_getUnique.
  auto.
Qed.


(** ** [isJoinId] etc. *)

Lemma isJoinId_eq : forall v,
  isJoinId v = match isJoinId_maybe v with | None => false |Some _ => true end.
Proof.
  unfold isJoinId.
  induction v; auto.
  now destruct i0.
Qed.

Lemma isJoinId_isJoinId_maybe: forall v,
  isJoinId v = true ->
  isJoinId_maybe v = Some (idJoinArity v).
Proof.
  unfold isJoinId.
  induction v; simpl; intros; auto; try discriminate.
  now destruct i0.
Qed.

Lemma idJoinArity_join: forall v a,
  isJoinId_maybe v = Some a -> idJoinArity v = a.
Proof.
  unfold isJoinId, isJoinId_maybe, idJoinArity.
  induction v; simpl; intros; auto; try discriminate.
  destruct i0; simpl; try discriminate.
  now inversion H.
Qed.


Axiom isJoinId_maybe_setIdOccInfo:
  forall v occ_info, 
  isJoinId_maybe (setIdOccInfo v occ_info) = isJoinId_maybe v.

Axiom isJoinId_maybe_asJoinId:
  forall v a,
  isJoinId_maybe (asJoinId v a) = Some a.
