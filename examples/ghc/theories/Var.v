From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Id.
Require Import Core. (* For [Var] only *)
Require Import Unique.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Structures.Equalities.
Require Import Coq.Classes.Morphisms.

Require Import GHC.Base.

Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.Traversable.

Require Import Proofs.Axioms.
Require Import Proofs.Unique.


Opaque Base.hs_string__.

Ltac unfold_zeze := 
  repeat (GHC.Base.unfold_zeze; unfold Core.Eq___Var, Core.Eq___Var_op_zeze__).
Ltac unfold_zsze :=
  repeat (GHC.Base.unfold_zsze; unfold Core.Eq___Var, Core.Eq___Var_op_zsze__).

(** ** Stuff about [Var] and [Unique] *)

Lemma getUnique_varUnique: 
    (Unique.getUnique : Var -> Unique.Unique) = varUnique.
Proof.
  unfold Unique.getUnique, Unique.getUnique__,Uniquable__Var,
     Core.Uniquable__Var_getUnique.
  auto.
Qed.


(** ** Properties about [GHC.Base.==] for Var. *)

(* Equal vars have equal keys *)
Lemma eq_unique : forall (v1 v2: Var), 
    (v1 == v2) <->
    Unique.getWordKey (Unique.getUnique v1) = 
    Unique.getWordKey (Unique.getUnique v2). 
Proof.
  intros v1 v2.
  unfold_zeze.
  unfold Unique.getUnique.
  unfold Uniquable__Var, getUnique__, Core.Uniquable__Var_getUnique, 
  varUnique.
  destruct v1; destruct v2; simpl;
  apply N.eqb_eq.
Qed.

Instance EqLaws_Var : EqLaws Var := {}.
Proof.
  - unfold ssrbool.reflexive.
    unfold_zeze.
    intros. unfold is_true.
    apply N.eqb_refl.
  - unfold ssrbool.symmetric.
    intros. unfold_zeze.
    rewrite N.eqb_sym; auto.
  - unfold ssrbool.transitive.
    unfold_zeze.
    unfold is_true.
    intros x y z. 
    destruct x; destruct y; destruct z; simpl;
    repeat erewrite N.eqb_eq; intro h; rewrite h; auto.
  - intros.
    unfold_zsze.
    unfold_zeze.
    rewrite negb_involutive.
    reflexivity.
Qed.


(** ** [varUnique] *)


Lemma varUnique_iff :
  forall v1 v2,
    v1 == v2 <-> varUnique v1 = varUnique v2.
Proof.
  intros.
  unfold_zeze.
  unfold varUnique.
  set (n1 := realUnique v1).
  set (n2 := realUnique v2).
  unfold is_true.
  rewrite N.eqb_eq.
  unfold Unique.mkUniqueGrimily in *.
  intuition congruence.
Qed.


Lemma In_varUnique_elem : forall a l, 
    In (varUnique a) (map varUnique l) <-> 
    Foldable.elem a l.
Proof.
  intros.
  induction l.
  - simpl. rewrite elem_nil.
    split; intro. contradiction. discriminate.
  - rewrite elem_cons.
    unfold is_true.
    rewrite orb_true_iff.
    split.
    intro h. inversion h.
    left. 
    rewrite <- varUnique_iff in *.
    apply Eq_Symmetric in H.
    auto.
    right. tauto.
    intro h.
    rewrite <- IHl in h.
    simpl.
    destruct h.
    left. 
    rewrite <- varUnique_iff in *.
    symmetry. auto.
    right. auto.
Qed.


Lemma var_eq_realUnique v1 v2 : 
  (v1 == v2) = (realUnique v1 == realUnique v2).
Proof.
  repeat unfold op_zeze__, op_zeze____,Core.Eq___Var_op_zeze__,Core.Eq___Var.
  auto.
Qed.



(** ** A DecidableType structure based on  [GHC.Base.==]. *)

(* Define the Var type as a decidable type by using the Eq instance.
   (This instance only looks at the Unique components of the Var *)

Module Var_as_DT <: BooleanDecidableType <: DecidableType.
  Definition t := Var.

  Definition eqb : t -> t -> bool := _==_.

  Definition eq : t -> t -> Prop := fun x y => eqb x y.

  Definition eq_equiv : Equivalence eq.
  Proof.
  split. 
  - unfold eq, eqb, Reflexive.
    apply Eq_refl.
  - unfold eq, eqb, Symmetric.
    eauto using Eq_sym.
  - unfold eq, eqb, Transitive.
    intros x y z h1 h2.
    eapply  Eq_trans; eauto.
  Defined.

  Definition eq_dec : forall x y : t, { eq x y } + { ~ (eq x y) }.
  Proof.
  intros x y.
  unfold eq, eqb.
  unfold_zeze.
  destruct x eqn:X; destruct y eqn:Y;  simpl.
  all: destruct (N.eqb realUnique realUnique0) eqn:EQ ; [left; auto | right; auto].
  Defined.

  Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
    unfold eq. tauto.
  Qed. 

 Definition eq_refl := eq_equiv.(@Equivalence_Reflexive _ _).
 Definition eq_sym := eq_equiv.(@Equivalence_Symmetric _ _).
 Definition eq_trans := eq_equiv.(@Equivalence_Transitive _ _).

End Var_as_DT.

Lemma realUnique_eq: forall v v',
    (realUnique v =? realUnique v')%N = Var_as_DT.eqb v v'.
Proof.
  intros.
  unfold Var_as_DT.eqb. cbn. reflexivity.
Qed.




(** ** [almostEqual] *)

(* Two [Var]s are almostEqual if they differ only in 
   their IdInfo. All other components must be identitical.

   We define this as a [Prop] rather than a bool because
   we do not have a function that determines structural
   equality.
*)

Inductive almostEqual : Var -> Var -> Prop :=
(*  | AE_TyVar   : forall n u ty,
   almostEqual (Mk_TyVar n u ty)
               (Mk_TyVar n u ty)  *)
(* | AE_TcTyVar : forall n u ty1 ty2,
   almostEqual (Mk_TcTyVar n u ty1 ty2)
               (Mk_TcTyVar n u ty1 ty2) *)
 | AE_Id : forall n u ty ids idd id1 id2,
   almostEqual (Mk_Id n u ty ids idd id1)
               (Mk_Id n u ty ids idd id2).


Lemma almostEqual_refl:
  forall v, almostEqual v v.
Proof. intros. destruct v; constructor. Qed.

Lemma almostEqual_sym:
  forall v1 v2,
    almostEqual v1 v2 -> almostEqual v2 v1.
Proof.
  intros v1 v2 H.
  inversion H; subst; eauto.
  econstructor.
Qed.

Lemma almostEqual_trans:
  forall v1 v2 v3, 
    almostEqual v1 v2 -> almostEqual v2 v3 -> almostEqual v1 v3.
Proof.
  intros v1 v2 v3 H1 H2. 
  inversion H1; inversion H2; subst; inversion H3; eauto.
  econstructor.
Qed.

Instance Equivalence_ae : Equivalence almostEqual.
Proof.
  split. 
  - unfold Reflexive.
    apply almostEqual_refl.
  - unfold Symmetric.
    eauto using almostEqual_sym.
  - unfold Transitive.
    intros x y z h1 h2.
    eapply almostEqual_trans; eauto.
Defined.

Lemma almostEqual_eq :
  forall v1 v2, 
    almostEqual v1 v2 -> (v1 == v2).
Proof.
  intros v1 v2 H.
  inversion H; unfold_zeze; simpl; apply N.eqb_refl.
Qed.

Instance eq_m :
  Proper ((fun (x y:Var) => x == y) ==> (fun x y => x == y) ==> Logic.eq) (fun (x y : Var) => (x == y)).
Proof.
  unfold_zeze.
  move=> x1 y1 E1 x2 y2 E2.
  apply N.eqb_eq in E1.
  apply N.eqb_eq in E2.
  rewrite E1. rewrite E2.
  eauto.
Qed.

Instance almostEqual_eq_m :
  Proper (almostEqual ==> almostEqual ==> Logic.eq) (fun (x y : Var) => (x == y)).
Proof.
  move=> x1 y1 E1 x2 y2 E2.
  apply almostEqual_eq in E1.
  apply almostEqual_eq in E2.
  rewrite -> E1.
  rewrite -> E2.
  auto.
Qed.


(** ** [isJoinId] etc. *)

Lemma isJoinId_eq : forall v,
  isJoinId v = match isJoinId_maybe v with | None => false |Some _ => true end.
Proof.
  unfold isJoinId.
  induction v; auto; simpl.
  unfold isJoinId_maybe; simpl.
  rewrite andb_false_r. 
  all: destruct id_details; done. 
Qed.

Lemma isJoinId_ae: forall v1 v2,
  almostEqual v1 v2 ->
  isJoinId v1 = isJoinId v2.
Proof.
  intros.
  induction H; reflexivity.
Qed.


Lemma isJoinId_isJoinId_maybe: forall v,
  isJoinId v = true ->
  isJoinId_maybe v = Some (idJoinArity v).
Proof.
  unfold isJoinId.
  induction v; simpl; intros; auto; try discriminate.
  destruct id_details; try discriminate.
  unfold idJoinArity,isJoinId_maybe; simpl.
  rewrite andb_false_r.
  reflexivity.
Qed.

Lemma idJoinArity_join: forall v a,
  isJoinId_maybe v = Some a -> idJoinArity v = a.
Proof.
  unfold isJoinId, isJoinId_maybe, idJoinArity.
  induction v; simpl; intros; auto; try discriminate.
  rewrite andb_false_r in H.
  destruct id_details; simpl; try discriminate.
  inversion H.
  unfold isJoinId_maybe; simpl.
  rewrite andb_false_r.
  simpl.
  reflexivity.
Qed.


(** ** [isLocalId] and [isLocalVar] *)


(* Local Vars include localIds as well as type/coercion vars *)

Lemma isLocalId_isLocalVar : 
  forall var, isLocalVar var = false -> isLocalId var = false.
Proof.
  intros var.
  unfold isLocalVar.
  unfold isGlobalId.
  unfold isLocalId. 
  destruct var.
  simpl. 
  all: try tauto.
  (* destruct idScope; done. *)
  move=>h. rewrite <- h.
  rewrite negb_involutive.
  auto. 
Qed.

Lemma isLocalVar_isLocalId : 
  forall var, isLocalId var = true -> isLocalVar var = true.
Proof.
  intros var.
  unfold isLocalVar.
  unfold isGlobalId.
  unfold isLocalId. 
  destruct var; simpl.
(*  destruct idScope; done. *)
  rewrite negb_involutive.
  auto. 
Qed.

(** ** isLocalVar respects the GHC.Base.== equality for Vars  *)

(* SCW: This is provable because we have modified the definition of isLocalVar 
   to look at the uniques instead of the scope. In GoodVars we know that these two 
   should be consistent with eachother.  So the remapping shouldn't matter as long 
   as all of the vars that we work with are good.
 *)
Definition RespectsVar (f :Var -> bool) :=
    Proper ((fun x0 y : Var => x0 == y) ==> Logic.eq) f.

Lemma RespectsVar_isLocalVar : RespectsVar isLocalVar.
Proof.
  move=> v1 v2.
  move=> h.
  rewrite -> varUnique_iff  in h.
  unfold isLocalVar. unfold isGlobalId. rewrite h.
  auto.
Qed.
Hint Resolve RespectsVar_isLocalVar.


Definition RespectsAEVar (f :Var -> bool) :=
    Proper ((fun x0 y : Var => almostEqual x0 y) ==> Logic.eq) f.
Lemma RespectsAEVar_isLocalVar : RespectsAEVar isLocalVar.
Proof.
  move=> v1 v2.
  move=> h.
  apply almostEqual_eq in h.
  rewrite -> varUnique_iff  in h.
  unfold isLocalVar. unfold isGlobalId. rewrite h.
  auto.
Qed.
Hint Resolve RespectsAEVar_isLocalVar.

(** ** [isTyVar] and [isCoVar] *)

Lemma isn'tTyVar v : isTyVar v = false.
Proof. by case: v. Qed.

Lemma isn'tCoVar v : isCoVar v = false.
Proof. by case: v. Qed.
