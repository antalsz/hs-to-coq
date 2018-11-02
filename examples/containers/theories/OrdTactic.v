(**

This module provides an [order] tactic that solves
goals involving the operations of a lawful [Ord] type class.

It is inspired by [Coq.Structures.OrdersTac], but does not use
the module system.
**)

Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Set Bullet Behavior "Strict Subproofs".

Class OrdLaws (t : Type) {HEq : Eq_ t} {HOrd : Ord t} {HEqLaw : EqLaws t} :=
  { (* The axioms *)
    Ord_antisym  : forall a b, a <= b = true -> b <= a = true -> a == b = true;
    Ord_trans_le : forall a b c, a <= b = true -> b <= c = true -> a <= c = true;
    Ord_total    : forall a b, a <= b = true \/ b <= a = true;
    (* The other operations, in terms of <= or == *)
    Ord_compare_Lt : forall a b, compare a b = Lt <-> b <= a = false;
    Ord_compare_Eq : forall a b, compare a b = Eq <-> a == b = true;
    Ord_compare_Gt : forall a b, compare a b = Gt <-> a <= b = false;
    Ord_lt_le : forall a b, a < b = negb (b <= a);
    Ord_ge_le : forall a b, a >= b = (b <= a);
    Ord_gt_le : forall a b, a >  b = negb (a <= b);
  }.

Module Lemmas.
Section Lemmas.
  Context {t : Type} {HEq : Eq_ t} {HOrd : Ord t} {HEqLaw : EqLaws t} {HOrdLaw : OrdLaws t}.

  Lemma Eq_neq_sym (x y : t) : (x == y) = false -> (y == x) = false.
  Proof. rewrite Eq_sym; auto. Qed.

  Lemma Eq_ne_eq (x y : t) : (x /= y) = negb (x == y).
  Proof. rewrite Eq_inv, negb_involutive; auto. Qed.

  Lemma Eq_eq_refl (x : t) : (x == x) = true.
  Proof. rewrite Eq_refl; auto. Qed.

  Lemma Ord_le_refl (x : t) : (x <= x) = true.
  Proof. destruct (Ord_total x x); auto. Qed.

  Lemma Eq_trans_l (x y z : t) : (x == y) = true -> (x == z) = (y == z).
  Proof.
    intros Exy; specialize (Eq_trans y x z Exy).
    destruct (y == z) eqn:Eyz.
    - intros H; rewrite H; auto. apply Eq_refl.
    - destruct (x == z) eqn:Exz; auto.
      exfalso.
      rewrite Eq_sym in Exz.
      specialize (Eq_trans _ _ _ Exz Exy); rewrite Eq_sym, Eyz.
      auto.
  Qed.

  Lemma Eq_trans_r (x y z : t) : (x == y) = true -> (z == x) = (z == y).
  Proof. rewrite (Eq_sym z x), (Eq_sym z y); apply Eq_trans_l. Qed.

  Lemma Eq_le_l (x y z : t) : (x == y) = true -> (x <= z) = (y <= z).
  Proof.
    intros Exy.
    rewrite <-Ord_compare_Eq in Exy;
      (destruct (x <= z) eqn:LExz; [|rename LExz into GTxz]);
      (destruct (y <= z) eqn:LEyz; [|rename LEyz into GTyz]);
      auto; exfalso.
    - apply not_true_iff_false in GTyz; apply GTyz; clear GTyz.
      apply Ord_trans_le with x; auto.
      rewrite <-not_false_iff_true, <-Ord_compare_Lt.
      congruence.
    - apply not_true_iff_false in GTxz; apply GTxz; clear GTxz.
      apply Ord_trans_le with y; auto.
      rewrite <-not_false_iff_true, <-Ord_compare_Gt.
      congruence.
  Qed.

  Lemma Eq_le_r (x y z : t) : (x == y) = true -> (z <= x) = (z <= y).
  Proof.
    intros Exy.
    rewrite <-Ord_compare_Eq in Exy;
      (destruct (z <= x) eqn:LEzx; [|rename LEzx into GTzx]);
      (destruct (z <= y) eqn:LEzy; [|rename LEzy into GTzy]);
      auto; exfalso.
    - apply not_true_iff_false in GTzy; apply GTzy; clear GTzy.
      apply Ord_trans_le with x; auto.
      rewrite <-not_false_iff_true, <-Ord_compare_Gt.
      congruence.
    - apply not_true_iff_false in GTzx; apply GTzx; clear GTzx.
      apply Ord_trans_le with y; auto.
      rewrite <-not_false_iff_true, <-Ord_compare_Lt.
      congruence.
  Qed.
  
  Lemma NEq_le_l (x y : t) : (x == y) = false -> (x <= y) = true -> (y <= x) = false.
  Proof.
    intros Nxy LExy.
    apply not_true_iff_false; intros LEyx.
    specialize (Ord_antisym _ _ LExy LEyx); rewrite Nxy; auto.
  Qed.

  Lemma NEq_le_r (x y : t) : (x == y) = false -> (y <= x) = true -> (x <= y) = false.
  Proof.
    intros Nxy LEyx.
    apply not_true_iff_false; intros LExy.
    specialize (Ord_antisym _ _ LExy LEyx); rewrite Nxy; auto.
  Qed.

  Lemma Ord_trans_lt (x y z : t) : y <= x = false -> z <= y = false -> z <= x = false.
  Proof.
    intros GTyx GTzy;
      apply not_true_iff_false in GTyx;
      apply not_true_iff_false in GTzy;
      apply not_true_iff_false;
      intros LEzx.
    destruct (Ord_total y x) as [? | LEyx]; try tauto.
    specialize (Ord_trans_le _ _ _ LEzx LEyx); auto.
  Qed.
  
  Lemma Ord_trans_lt_le (x y z : t) : y <= x = false -> y <= z = true -> z <= x = false.
  Proof.
    intros GTyx LEyz;
      apply not_true_iff_false in GTyx;
      apply not_true_iff_false;
      intros LEzx.
    specialize (Ord_trans_le _ _ _ LEyz LEzx); auto.
  Qed.
      

  Lemma Ord_trans_le_lt (x y z : t) : x <= y = true -> z <= y = false -> z <= x = false.
  Proof.
    intros LExy GTzy;
      apply not_true_iff_false in GTzy;
      apply not_true_iff_false;
      intros LEzx.
    specialize (Ord_trans_le _ _ _ LEzx LExy); auto.
  Qed.
End Lemmas.
End Lemmas.

(* Translate `bool` manipulation to `Prop` manipulation, and get rid of ssreflect *)

Ltac not_bool_const b :=
  match b with
  | true  => fail 1
  | false => fail 1
  | _     => idtac
  end.

Ltac nonconst_bool_eq_to_iff :=
  repeat match goal with
  | H : context[?b1 = ?b2 :> bool] |- _ =>
    not_bool_const b1; not_bool_const b2; rewrite ->eq_iff_eq_true in H
  | |- context[?b1 = ?b2 :> bool] =>
    not_bool_const b1; not_bool_const b2; rewrite ->eq_iff_eq_true
  end.

Hint Rewrite -> andb_true_iff : bool_to_prop.
Hint Rewrite -> orb_true_iff  : bool_to_prop.
Hint Rewrite -> negb_true_iff : bool_to_prop.

Ltac bool_to_prop :=
  nonconst_bool_eq_to_iff;
  unfold is_true in *;
  autorewrite with bool_to_prop in *.

(* `order` tactic *)

Ltac order_prepare t :=
 lazymatch goal with
 | H : ?A -> False |- _ => change (~A) in H; order_prepare t
 | H : _ <> true   |- _ => rewrite not_true_iff_false in H; order_prepare t
 | H : _ <> false  |- _ => rewrite not_false_iff_true in H; order_prepare t
 | H : negb ?b = true |- _ => rewrite negb_true_iff in H; order_prepare t
 | H : negb ?b = false |- _ => rewrite negb_false_iff in H; order_prepare t
 | H : @op_zsze__ t _   ?x ?y = ?b |- _ => rewrite Lemmas.Eq_ne_eq in H; order_prepare t
 | H : @op_zl__   t _ _ ?x ?y = ?b |- _ => rewrite Ord_lt_le in H; order_prepare t
 | H : @op_zgze__ t _ _ ?x ?y = ?b |- _ => rewrite Ord_ge_le in H; order_prepare t
 | H : @op_zg__   t _ _ ?x ?y = ?b |- _ => rewrite Ord_gt_le in H; order_prepare t
 | H : @compare   t _ _ ?x ?y = Eq |- _ => rewrite Ord_compare_Eq in H; order_prepare t
 | H : @compare   t _ _ ?x ?y = Lt |- _ => rewrite Ord_compare_Lt in H; order_prepare t
 | H : @compare   t _ _ ?x ?y = Gt |- _ => rewrite Ord_compare_Gt in H; order_prepare t
 | |- @compare   t _ _ ?x ?y = Eq => rewrite Ord_compare_Eq; order_prepare t
 | |- @compare   t _ _ ?x ?y = Lt => rewrite Ord_compare_Lt; order_prepare t
 | |- @compare   t _ _ ?x ?y = Gt => rewrite Ord_compare_Gt; order_prepare t
 (* reorient *)
 | H : true  = @op_zeze__ t _   ?x ?y |- _ => symmetry in H; order_prepare t
 | H : false = @op_zeze__ t _   ?x ?y |- _ => symmetry in H; order_prepare t
 | |-  true  = @op_zeze__ t _   ?x ?y      => symmetry;      order_prepare t
 | |-  false = @op_zeze__ t _   ?x ?y      => symmetry;      order_prepare t
 | H : true  = @op_zlze__ t _ _ ?x ?y |- _ => symmetry in H; order_prepare t
 | H : false = @op_zlze__ t _ _ ?x ?y |- _ => symmetry in H; order_prepare t
 | |-  true  = @op_zlze__ t _ _ ?x ?y      => symmetry;      order_prepare t
 | |-  false = @op_zlze__ t _ _ ?x ?y      => symmetry;      order_prepare t
 (* pull things out of the conclusion *)
 | |- _ = true  => apply not_false_is_true; intro; order_prepare t
 | |- _ = false => apply not_true_is_false; intro; order_prepare t
 (* otherwise, hope it's contradictory *)
 | _ => exfalso
 end.

Definition HIDE (P : Prop) := P.
Lemma hide : forall {P : Prop},  P -> HIDE P. Proof. intuition. Qed.
Lemma unhide : forall {P : Prop},  HIDE P -> P. Proof. intuition. Qed.

Ltac order_eq t x y Heq :=
  apply hide in Heq;
  repeat lazymatch goal with
  | H : @op_zeze__ t _ x ?z = ?b |- _ =>
    rewrite (@Lemmas.Eq_trans_l t _ _ x y z (unhide Heq)) in H
  | H : @op_zeze__ t _ ?z x = ?b |- _ =>
    rewrite (@Lemmas.Eq_trans_r t _ _ x y z (unhide Heq)) in H
  | H : @op_zlze__ t _ _ x ?z = ?b |- _ =>
    rewrite (@Lemmas.Eq_le_l t _ _ _ _ x y z (unhide Heq)) in H
  | H : @op_zlze__ t _ _ ?z x = ?b |- _ =>
    rewrite (@Lemmas.Eq_le_r t _ _ _ _ x y z (unhide Heq)) in H
  end;
  clear Heq.

Ltac pose_new prf :=
  let prop := type of prf in
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => pose proof prf
  end.


Ltac order_loop t :=
 lazymatch goal with
 | H1 : ?x = true, H2 : ?x = false |- _  => congruence
 (* First, successful situations *)
 | H : @op_zeze__ t _   ?x ?x = false |- _ => rewrite Lemmas.Eq_eq_refl in H; congruence
 | H : @op_zlze__ t _ _ ?x ?x = false |- _ => rewrite Lemmas.Ord_le_refl in H; congruence
 (* Second, useless hyps *)
 | H : @op_zeze__ t _   ?x ?x = true |- _ => clear H; order_loop t
 | H : @op_zlze__ t _ _ ?x ?x = true |- _ => clear H; order_loop t
 (* Third, we eliminate equalities *)
 | H : @op_zeze__ t _ ?x ?y = true |- _ =>
     order_eq t x y H; order_loop t
 (* Simultaneous le and ge is eq *)
 | H1 : @op_zlze__ t _ _ ?x ?y = true, H2 : @op_zlze__ t _ _  ?y ?x = true |- _ =>
     pose proof (@Ord_antisym t _ _ _ _ x y H1 H2); clear H1 H2; order_loop t
 (* Simultaneous le and ~eq is lt *)
 | H1 : @op_zeze__ t _ ?x ?y = false, H2 : @op_zlze__ t _ _  ?x ?y = true |- _ =>
     apply (@Lemmas.NEq_le_l t _ _ _ _ x y H1) in H2; order_loop t
 | H1 : @op_zeze__ t _ ?x ?y = false, H2 : @op_zlze__ t _ _  ?y ?x = true |- _ =>
     apply (@Lemmas.NEq_le_r t _ _ _ _ x y H1) in H2; order_loop t
 | _ => match goal with
   (* Transitivity of lt and le *)
   (* Here we need back-tracking, because we expect [pose_new] to fail.
      I would love if once [pose_new] succeeds, no backtracking happens
      even when the recursive call fails, but I do not know how to do that. *)
   | H1 : @op_zlze__ t _ _ ?x ?y = true, H2 : @op_zlze__ t _ _ ?y ?z = true |- _ =>
       pose_new (@Ord_trans_le t _ _ _ _ x y z H1 H2); order_loop t
   | H1 : @op_zlze__ t _ _ ?y ?x = false, H2 : @op_zlze__ t _ _ ?z ?y = false |- _ =>
       pose_new (@Lemmas.Ord_trans_lt t _ _ _ _ x y z H1 H2); order_loop t
   | H1 : @op_zlze__ t _ _ ?x ?y = true, H2 : @op_zlze__ t _ _ ?z ?y = false |- _ =>
       pose_new (@Lemmas.Ord_trans_le_lt t _ _ _ _ x y z H1 H2); order_loop t
   | H1 : @op_zlze__ t _ _ ?y ?x = false, H2 : @op_zlze__ t _ _ ?y ?z = true |- _ =>
       pose_new (@Lemmas.Ord_trans_lt_le t _ _ _ _ x y z H1 H2); order_loop t
   (* Nothing left to do *)
   | _ => idtac
   end
end.

(* TODO: Can't handle disjunctions *)
Ltac order t :=
 solve [ repeat (intros; try red);
         bool_to_prop;
         intuition (solve [try subst; try easy;
                           order_prepare t; order_loop t])
       | fail 1 "order can't solve this system" ].

(** Flipping comparisons **)

Definition flip_comparison (c : comparison) := match c with
  | Lt => Gt
  | Eq => Eq
  | Gt => Lt
  end.

Theorem compare_flip {t : Type} `{OrdLaws t} (x y : t) :
  compare x y = flip_comparison (compare y x).
Proof.
  destruct (compare x y) eqn:Cxy; destruct (compare y x) eqn:Cyx; simpl; auto; order t.
Qed.

Theorem flip_comparison_involutive :
  ssrfun.involutive flip_comparison.
Proof. now repeat red; destruct 0. Qed.

Theorem flip_comparison_injective :
  ssrfun.injective flip_comparison.
Proof. now repeat red; repeat destruct 0. Qed.

Theorem compare_flip_iff {A} `{OrdLaws A} (x y : A) (c : comparison) :
  compare x y = c <-> compare y x = flip_comparison c.
Proof.
  split.
  - now intro; subst; rewrite compare_flip.
  - rewrite compare_flip; apply flip_comparison_injective.
Qed.

(** Lawfulness of [ord_default] *)

Section GoodCompare.
Context {t : Type} {HEq : Eq_ t} {HEqLaw : EqLaws t}.
Variable (compare : t -> t -> comparison).

Record GoodCompare :=
  { Good_compare_Eq : forall a b, compare a b = Eq <-> a == b = true;
    Good_compare_sym : forall a b, compare a b = flip_comparison (compare b a);
    Good_compare_trans_1 : forall a b c, compare a b = Lt -> compare b c = Lt -> compare a c = Lt;
    Good_compare_trans_2 : forall a b c, compare a b = Lt -> compare b c = Eq -> compare a c = Lt;
    Good_compare_trans_3 : forall a b c, compare a b = Eq -> compare b c = Lt -> compare a c = Lt;
  }.

Lemma Good_compare_sym_Eq (HGood : GoodCompare) : forall a b, compare a b = Eq <-> compare b a = Eq.
Proof. intros. rewrite (Good_compare_sym HGood). destruct (compare b a); simpl; intuition congruence. Qed.

Lemma  OrdLaws_ord_default (HGood : GoodCompare) : OrdLaws t (HOrd := ord_default compare).
Proof.
  split.
  * intros.
    unfold op_zlze__, ord_default, op_zlze____ in *.
    rewrite <- (Good_compare_Eq HGood).
    rewrite (Good_compare_sym HGood) in H.
    destruct (compare a b); simpl in *; congruence.
  * intros.
    unfold op_zlze__, ord_default, op_zlze____ in *.
    destruct (compare b a) eqn:H1, (compare c b) eqn:H2, (compare c a) eqn:H3; simpl in *;
        try congruence; exfalso.
    - rewrite (Good_compare_Eq HGood) in H1, H2.
      enough (compare c a = Eq) by congruence.
      rewrite (Good_compare_Eq HGood).
      eapply Eq_trans; eassumption.
    - enough (compare c b = Lt) by congruence.
      rewrite (Good_compare_sym_Eq HGood) in H1.
      eapply (Good_compare_trans_2 HGood); try eassumption.
    - enough (compare b a = Lt) by congruence.
      rewrite (Good_compare_sym_Eq HGood) in H2.
      eapply (Good_compare_trans_3 HGood); try eassumption.
    - assert (compare b c = Lt) by (rewrite (Good_compare_sym HGood); destruct (compare c b); simpl in *; congruence).
      enough (compare b a = Lt) by congruence.
      eapply (Good_compare_trans_1 HGood); try eassumption.
  * intros.
    unfold op_zlze__, ord_default, op_zlze____ in *.
    rewrite (Good_compare_sym HGood).
    destruct (compare a b); simpl; intuition.
  * intros.
    unfold op_zlze__, Base.compare, ord_default, op_zlze____, compare__ in *.
    destruct (compare a b); simpl; intuition congruence.
  * intros.
    unfold op_zlze__, Base.compare, ord_default, op_zlze____, compare__ in *.
    rewrite (Good_compare_Eq HGood).
    reflexivity.
  * intros.
    unfold op_zlze__, Base.compare, ord_default, op_zlze____, compare__ in *.
    rewrite (Good_compare_sym HGood).
    destruct (compare b a); simpl; intuition congruence.
  * intros.
    unfold op_zlze__, op_zl__, Base.compare, ord_default, op_zlze____, op_zl____, compare__ in *.
    destruct (compare a b); simpl; intuition congruence.
  * intros.
    unfold op_zgze__, op_zlze__, Base.compare, ord_default, op_zgze____, op_zlze____, compare__ in *.
    destruct (compare a b); simpl; intuition congruence.
  * intros.
    unfold op_zg__, op_zlze__, Base.compare, ord_default, op_zg____, op_zlze____, compare__ in *.
    rewrite (Good_compare_sym HGood).
    destruct (compare a b); simpl; intuition congruence.
Qed.
End GoodCompare.

(** good comparison functions transfer *)

Section GoodCompareImage.
Context (t1 : Type) {HEq1 : Eq_ t1} {HEqLaw1 : EqLaws t1}.
Context (t2 : Type) {HEq2 : Eq_ t2}  (* {HEqLaw2 : EqLaws t2} *).
Context (f : t2 -> t1).
Context (Eq_t2 : forall x y, (x == y) = (f x == f y)).
Context {compare : t1 -> t1 -> comparison}.
Context (HGood : GoodCompare compare).

Lemma GoodCompare_image : GoodCompare (fun x y => compare (f x) (f y)).
Proof.
  split.
  * intros. rewrite Eq_t2. rewrite (Good_compare_Eq _ HGood). reflexivity.
  * intros. rewrite (Good_compare_sym _ HGood). reflexivity.
  * intros. eapply (Good_compare_trans_1 _ HGood); eassumption.
  * intros. eapply (Good_compare_trans_2 _ HGood); eassumption.
  * intros. eapply (Good_compare_trans_3 _ HGood); eassumption.
Qed.

End GoodCompareImage.

(** Lawfulness of the list instance *)
Section ListOrd.
Context  a {HEq : Eq_ a} {HOrd : Ord a} {HEqLaw : EqLaws a} {HOrdLaw : OrdLaws a}.

Lemma GoodCompare_compare_list : GoodCompare compare_list.
Proof.
  constructor.
  - unfold "==", Eq_list; simpl.
    intros xs; induction xs as [|x xs IH]; intros [|y ys]; simpl;
      try solve [tauto | split; discriminate].
    destruct (compare x y) eqn:Cxy.
    all: try (split; [discriminate|]).
    all: try (rewrite andb_true_iff, <-Ord_compare_Eq; intros [? ?]; congruence).
    rewrite Ord_compare_Eq in Cxy.
    rewrite IH, Cxy; tauto.
  - intros xs; induction xs as [|x xs IH]; intros [|y ys]; simpl;
      try tauto.
    rewrite compare_flip; destruct (compare y x) eqn:Cyx; simpl; auto.
  - intros xs; induction xs as [|x xs IH]; intros [|y ys] [|z zs]; simpl;
      try solve [tauto | discriminate].
    idtac;
      destruct (compare x y) eqn:Cxy; try discriminate;
      destruct (compare y z) eqn:Cyz; try discriminate;
      destruct (compare x z) eqn:Cxz; try discriminate;
      auto; try apply IH;
      order a.
  - intros xs; induction xs as [|x xs IH]; intros [|y ys] [|z zs]; simpl;
      try solve [tauto | discriminate].
    idtac;
      destruct (compare x y) eqn:Cxy; try discriminate;
      destruct (compare y z) eqn:Cyz; try discriminate;
      destruct (compare x z) eqn:Cxz; try discriminate;
      auto; try apply IH;
      order a.
  - intros xs; induction xs as [|x xs IH]; intros [|y ys] [|z zs]; simpl;
      try solve [tauto | discriminate].
    idtac;
      destruct (compare x y) eqn:Cxy; try discriminate;
      destruct (compare y z) eqn:Cyz; try discriminate;
      destruct (compare x z) eqn:Cxz; try discriminate;
      auto; try apply IH;
      order a.
Qed.

Global Instance OrdLaws_list  : OrdLaws (list a)
  := OrdLaws_ord_default _ GoodCompare_compare_list.
End ListOrd.


Ltac unfoldN := unfold
  op_zeze__, op_zgze__, op_zlze__, op_zl__, op_zg__, compare,
  Eq_Integer___, Ord_Char___,
  op_zeze____, op_zgze____, op_zlze____, op_zl____, op_zg____, compare__
  in *.

Instance OrdLaws_N : OrdLaws N := {}.
Proof.
  all: intros; unfoldN;
    rewrite ?N.eqb_eq, ?N.leb_le in *;
    try apply eq_iff_eq_true; 
    rewrite ?negb_true_iff, ?N.eqb_eq, ?N.eqb_neq, ?N.leb_le,  ?N.leb_gt, ?N.ltb_lt,
            ?N.compare_eq_iff, ?N.compare_lt_iff, ?N.compare_gt_iff in *;
    try (zify;omega).
Qed.

Ltac unfoldZ := unfold
  op_zeze__, op_zgze__, op_zlze__, op_zl__, op_zg__, compare,
  Eq_Integer___, Ord_Integer___,
  op_zeze____, op_zgze____, op_zlze____, op_zl____, op_zg____, compare__
  in *.

Instance OrdLaws_Z : OrdLaws Z := {}.
Proof.
  all: intros; unfoldZ;
    rewrite ?Z.eqb_eq, ?Z.leb_le in *;
    try apply eq_iff_eq_true; 
    rewrite ?negb_true_iff, ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_le,  ?Z.leb_gt, ?Z.ltb_lt,
            ?Z.compare_eq_iff, ?Z.compare_lt_iff, ?Z.compare_gt_iff in *;
    try omega.
Qed.

Module Tests.
Goal forall x : Z, x == x = true.
Proof. order Z. Qed.

Goal forall x : Z, (x /= x) = true -> False.
Proof. order Z. Qed.

Goal forall x : Z, ~ (x /= x = false) -> False.
Proof. order Z. Qed.

Goal forall x : Z, (x <= x) = false -> False.
Proof. order Z. Qed.

Goal forall x : Z, x < x = false.
Proof. order Z. Qed.

Goal forall x y : Z, x <= y = true -> y <= x = true -> x == y = true.
Proof. order Z. Qed.

Goal forall x y z : Z, x <= y = true -> y <= z = true -> x <= z = true.
Proof. order Z. Qed.

Goal forall x y z : Z, x <= y = true -> x == y = false -> y <= x = false.
Proof. order Z. Qed.

Goal forall x y z : Z, x <= y = true -> y <= x = true -> y <= z = true -> x <= z = true.
Proof. order Z. Qed.

Goal forall x y z : Z, x < y = true -> y < z = true -> x < z = true.
Proof. order Z. Qed.

Goal forall x y z : Z, x < y = true -> x <= y = true.
Proof. order Z. Qed.

Goal forall x y z a: Z, x < y = true -> y <= z = true -> z < a = true -> x < a = true.
Proof. order Z. Qed.

Goal forall x y z a: Z, x < y = true -> y <= z = true -> z < a = true -> a <= x = true -> False.
Proof. order Z. Qed.

Goal forall x y : Z, compare x y = Eq <-> x == y = true.
Proof. order Z. Qed.

Goal forall x y z : Z, x < y = true -> y > x = true.
Proof. order Z. Qed.


End Tests.
