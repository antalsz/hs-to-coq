Require Import Coq.Relations.Relation_Operators.
Require Import Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Classes.RelationClasses.
Require Import Omega.


Definition compose A (R S : relation A) : relation A :=
  fun x y => exists z, R x z /\ S z y.
(*Heavily based on the Lex proofs from the CoLoR library. The main difference is that I need the 
  first relation to be on the second type in the tuple because of the order of the arguments in the
  Haskell functions*)
Section Lex.
  Variables (A B : Type) (ltA eqA : relation A) (ltB : relation B).
  Inductive lex : relation (B * A) :=
  | lex1 a a' b b' : ltA a a' -> lex (b,a) (b',a')
  | lex2 a a' b b' : eqA a a' -> ltB b b' -> lex (b,a) (b',a').
  Variables (WF_gtA : well_founded ltA) (WF_gtB : well_founded ltB)
    (eqA_trans : Transitive eqA) (Hcomp : forall x y : A, (exists z : A, eqA y z /\ ltA x z) -> ltA x y)
    (eqA_sym: Symmetric eqA).
  
   Lemma lex_Acc_eq : forall a b,
    Acc lex (b,a) -> forall a', eqA a a' -> Acc lex (b,a').

  Proof.
    intros a b SN_ab a' eqaa'. inversion SN_ab. apply Acc_intro.
    destruct y as (a'',b'). intro H'.
    inversion H'; subst a'0 b'0 a0 b0; apply H.
    apply lex1. apply Hcomp. exists a'. auto. 
    apply lex2. assert (eqA a' b'). eapply eqA_sym. assumption. 
    pose proof (eqA_trans _ _ _ eqaa' H0). apply eqA_sym. assumption. assumption.
  Qed.

  Lemma lex_Acc :
    forall a, Acc ltA a -> forall b, Acc ltB b -> Acc lex (b, a).

  Proof.
    induction 1 as [a Ha1 Ha2]. induction 1 as [b Hb1 Hb2]. apply Acc_intro.
    destruct y as (a'',b'). intro H. inversion H. subst a'' b'0. subst a0. subst a'. (* subst a'' b'0 a0 b0.*)
    (* gtA a a' *)
    apply Ha2. exact H1. apply WF_gtB. 
    (* eqA a a' /\ gtB b b' *)
    apply (@lex_Acc_eq a).
    apply Hb2. assumption. apply eqA_sym. assumption.
  Qed.

  Lemma WF_lex : well_founded lex.

  Proof.
    unfold well_founded. destruct a as (a,b). apply lex_Acc. apply WF_gtA. apply WF_gtB.
  Qed.

End Lex.

Definition f_nat_lt {a} (f: a -> nat) x y := f x < f y.

Lemma f_nat_lt_acc: forall {a} (f: a -> nat) x n, f x <= n -> Acc (f_nat_lt f) x.
Proof.
  intros. generalize dependent x. induction n; auto.
  - intros. apply Acc_intro. intros. unfold f_nat_lt in *. omega.
  - unfold f_nat_lt in *. intros. apply Acc_intro. intros. apply IHn. omega.
Qed.

Lemma f_nat_lt_wf: forall {a} (f: a -> nat), well_founded (f_nat_lt f).
Proof.
  red. intro. intro. intro. eapply f_nat_lt_acc. eauto.
Qed.
