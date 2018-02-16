(**

This module provides an [order] tactic that solves
goals involving the operations of a lawful [Ord] type class.

It is inspired by [Coq.Structures.OrdersTac], but does not use
the module system.
**)

Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.

Class OrdLaws (t : Type) {HEq : Eq_ t} {HOrd : Ord t} {HEqLaw : EqLaws t} :=
  { (* The axioms *)
    Ord_antisym  : forall a b, a <= b = true -> b <= a = true -> a == b = true;
    Ord_trans_le : forall a b c, a <= b = true -> b <= c = true -> a <= c = true;
    Ord_total    : forall a b, a <= b = true \/ b <= a = true;
    (* The other operations, in terms of <= or == *)
    Ord_compare_Lt : forall a b, compare a b = Lt <-> b <= a = false;
    Ord_compare_Eq : forall a b, compare a b = Eq <-> b == a = true;
    Ord_compare_Gt : forall a b, compare a b = Gt <-> a <= b = false;
    Ord_lt_le : forall a b, a < b = negb (b <= a);
    Ord_ge_le : forall a b, a >= b = (b <= a);
    Ord_gt_le : forall a b, a >  b = negb (a <= b);
  }.

Section Lemmas.
  Context {t : Type} {HEq : Eq_ t} {HOrd : Ord t} {HEqLaw : EqLaws t}.

  Lemma Eq_ne_eq : forall x y : t, (x /= y) = negb (x == y).
  Admitted.

  Lemma Eq_eq_refl : forall x : t, (x == x) = true.
  Admitted.

  Lemma Ord_le_refl : forall x : t, (x <= x) = true.
  Admitted.


End Lemmas.

Ltac order_prepare t :=
 match goal with
 | H : ?A -> False |- _ => change (~A) in H; order_prepare t
 | H : _ <> true   |- _ => rewrite not_true_iff_false in H; order_prepare t
 | H : _ <> false  |- _ => rewrite not_false_iff_true in H; order_prepare t
 | H : negb ?b = true |- _ => rewrite negb_true_iff in H; order_prepare t
 | H : negb ?b = false |- _ => rewrite negb_false_iff in H; order_prepare t
 | H : @op_zsze__ t _   ?x ?y = ?b |- _ => rewrite Eq_ne_eq in H; order_prepare t
 | H : @op_zl__   t _ _ ?x ?y = ?b |- _ => rewrite Ord_lt_le in H; order_prepare t
 | H : @op_zgze__ t _ _ ?x ?y = ?b |- _ => rewrite Ord_ge_le in H; order_prepare t
 | H : @op_zg__   t _ _ ?x ?y = ?b |- _ => rewrite Ord_gt_le in H; order_prepare t

 (*
 | H : ~(?R ?x ?y) |- _ =>
   match R with
   | eq => fail 1 (* if already using [eq], we leave it this ways *)
   | _ => (change (~x==y) in H ||
           apply not_gt_le in H ||
           apply not_ge_lt in H ||
           clear H || fail 1); order_prepare
   end
 | H : ?R ?x ?y |- _ =>
   match R with
   | eq => fail 1
   | lt => fail 1
   | le => fail 1
   | _ => (change (x==y) in H ||
           change (x<y) in H ||
           change (x<=y) in H ||
           clear H || fail 1); order_prepare
   end
 | |- ~ _ => intro; order_prepare
 | |- _ ?x ?x =>
   exact (eq_refl x) || exact (le_refl x) || exfalso
 | _ =>
   (apply not_neq_eq; intro) ||
   (apply not_ge_lt; intro) ||
   (apply not_gt_le; intro) || exfalso
 *)
 | |- _ = true  => apply not_false_is_true; intro; order_prepare t
 | |- _ = false => apply not_true_is_false; intro; order_prepare t
 | _ => exfalso
 end.

Ltac order_loop t :=
 match goal with
 (* First, successful situations *)
 | H : @op_zeze__ t _ ?x ?x = false |- _ => rewrite Eq_eq_refl in H; congruence
 | H : @op_zlze__ t _ _ ?x ?x = false |- _ => rewrite Ord_le_refl in H; congruence
 (* Second, useless hyps *)
 | H : @op_zlze__ t _ _ ?x ?x = true |- _ => rewrite Ord_le_refl in H; order_loop t
 (* Third, we eliminate equalities *)
 (*
 | H : ?x == ?y |- _ => order_eq x y H; order_loop
 (* Simultaneous le and ge is eq *)
 | H1 : ?x <= ?y, H2 : ?y <= ?x |- _ =>
     generalize (le_antisym H1 H2); clear H1 H2; intro; order_loop
 (* Simultaneous le and ~eq is lt *)
 | H1: ?x <= ?y, H2: ~ ?x == ?y |- _ =>
     generalize (le_neq_lt H1 H2); clear H1 H2; intro; order_loop
 | H1: ?x <= ?y, H2: ~ ?y == ?x |- _ =>
     generalize (le_neq_lt H1 (neq_sym H2)); clear H1 H2; intro; order_loop
 (* Transitivity of lt and le *)
 | H1 : ?x < ?y, H2 : ?y < ?z |- _ =>
    match goal with
      | H : x < z |- _ => fail 1
      | _ => generalize (lt_trans H1 H2); intro; order_loop
    end
 | H1 : ?x <= ?y, H2 : ?y < ?z |- _ =>
    match goal with
      | H : x < z |- _ => fail 1
      | _ => generalize (le_lt_trans H1 H2); intro; order_loop
    end
 | H1 : ?x < ?y, H2 : ?y <= ?z |- _ =>
    match goal with
      | H : x < z |- _ => fail 1
      | _ => generalize (lt_le_trans H1 H2); intro; order_loop
    end
 | H1 : ?x <= ?y, H2 : ?y <= ?z |- _ =>
    match goal with
      | H : x <= z |- _ => fail 1
      | _ => generalize (le_trans H1 H2); intro; order_loop
    end *)
 | _ => idtac
end.


Ltac order t :=
 intros; order_prepare t; order_loop t.


Module Tests.

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

Lemma test1 : forall x : Z, x == x = true.
Proof. order Z. Qed.

Lemma test2 : forall x : Z, (x /= x) = true -> False.
Proof. order Z. Qed.

Lemma test3 : forall x : Z, ~ (x /= x = false) -> False.
Proof. order Z. Qed.

Lemma test4 : forall x : Z, (x <= x) = false -> False.
Proof. order Z. Qed.

Lemma test5 : forall x : Z, x < x = false.
Proof. order Z. Qed.


End Tests.
