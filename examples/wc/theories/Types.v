Require Export Types.

Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Foldable.

Require Import GHC.List.
Require GHC.Char.

Require Import ssrbool ssreflect.

Definition eq_CharType (x : CharType) (y:CharType) :=
  match x , y with 
    | IsSpace , IsSpace => true
    | NotSpace, NotSpace => true
    | _ , _ => false
  end.

Instance Eq_CharType : Eq_ CharType := eq_default eq_CharType.

Instance EqLaws_CharType : EqLaws CharType. Admitted.

Instance EqExact_CharType : EqExact CharType.
constructor; intros x y.
apply iff_reflect. split.
- inversion 1. apply Eq_refl.
- destruct x; destruct y; inversion 1; reflexivity.
Qed.

Fixpoint eq_flux (x : Flux) (y: Flux) : bool :=
  match x , y with 
  | Mk_Flux c1 i c2 , Mk_Flux d1 j d2 => 
    (c1 == d1) && (i == j) && (c2 == d2)
  | Unknown , Unknown => true
  | _ , _ => false 
  end.

Instance Eq_Flux : Eq_ Flux := eq_default eq_flux.

Instance EqLaws_Flux : EqLaws Flux. Admitted.

Instance EqExactFlux : EqExact Flux.
Proof.
  constructor; intros x y.
  apply iff_reflect. split.
  - intro h. subst. apply Eq_reflI. reflexivity.
  - generalize dependent y. induction x.
    + destruct y.
      * unfold op_zeze__, Eq_Flux, eq_default. simpl.
        move /andP => [H1 H2]. move /andP in H1. destruct H1.
        move /Eq_eq in H. move /Eq_eq in H2. move /Eq_eq in H0.
        subst. reflexivity.
      * inversion 1.
    + destruct y; inversion 1. reflexivity.
Qed.

Instance SemigroupLaws_Flux : SemigroupLaws Flux.
Proof.
  constructor.
  intros x y z.
  destruct x eqn:Hx; destruct y eqn:Hy; destruct z eqn:Hz;  
    unfold op_zlzlzgzg__, Semigroup__Flux, Types.Semigroup__Flux_op_zlzlzgzg__; simpl.
  all: try destruct c0.
  all: try destruct c1.
  all: try destruct c2.
  all: try destruct c3.
  all: apply Eq_reflI; f_equal.
  all: try reflexivity.
  all: omega.
Qed.

Instance Lawful_Flux : MonoidLaws Flux.
constructor.
+ intros x. apply Eq_reflI. reflexivity.
+ intros x. destruct x. apply Eq_reflI. 
  unfold mappend, mempty, Monoid__Flux , mappend__ , mempty__, Types.Monoid__Flux_mempty . 
  unfold Types.Monoid__Flux_mappend.
  unfold op_zlzlzgzg__, Semigroup__Flux, Types.Semigroup__Flux_op_zlzlzgzg__; simpl.
  destruct c0; reflexivity.
  apply Eq_reflI. reflexivity.
+ intros x y. apply Eq_reflI. reflexivity.
+ intros x. apply Eq_reflI. reflexivity.
Qed.

Definition eq_counts (x:Counts) (y:Counts) : bool := 
  match x , y with
    | Mk_Counts x1 x2 x3, Mk_Counts y1 y2 y3 => 
      (x1 == y1) && (x2 == y2) && (x3 == y3)
  end.

Instance Eq_Counts : Eq_ Counts := eq_default eq_counts.

Instance EqLaws_Counts : EqLaws Counts. Admitted.

Instance EqExact_Counts : EqExact Counts.
constructor; intros x y.
apply iff_reflect. split.
- inversion 1. apply Eq_refl.
- destruct x; destruct y.
  unfold op_zeze__, Eq_Counts, eq_default. simpl.
  move /andP => [H1 H2]. move /andP in H1. destruct H1.
  move /Eq_eq in H. move /Eq_eq in H2. move /Eq_eq in H0.
  subst. reflexivity.
Qed.  

Instance SemigroupLaws_Counts : SemigroupLaws Counts.
Proof.
  constructor.
  intros x y z.
  destruct x eqn:Hx; destruct y eqn:Hy; destruct z eqn:Hz;  
    unfold op_zlzlzgzg__, Semigroup__Counts, Types.Semigroup__Counts_op_zlzlzgzg__; simpl.
  unfold op_zeze__, Eq_Counts, eq_default, op_zeze____,eq_counts .
Admitted.

Instance MonoidLaws_Counts : MonoidLaws Counts.
Proof.
  constructor.
  + intros x. destruct x. apply Eq_reflI. reflexivity.
  + intros x. destruct x. apply Eq_reflI. 
  unfold mappend, mempty, Monoid__Counts , mappend__ , mempty__, Types.Monoid__Counts_mempty . 
  unfold Types.Monoid__Counts_mappend.
  unfold op_zlzlzgzg__, Semigroup__Counts, Types.Semigroup__Counts_op_zlzlzgzg__; simpl.
  f_equal. omega. admit. omega.
  + intros x y. apply Eq_reflI. reflexivity.
  + intros x. apply Eq_reflI. reflexivity.
Admitted.

Lemma Counts_assoc : forall x y z : Counts, ((x <<>> (y <<>> z)) = ((x <<>> y) <<>> z)).
  intros x y z. apply /Eq_eq.
  eapply semigroup_assoc; eauto.
Qed.
