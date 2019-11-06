Require Import Types.
Require BL.

Require Import Stupid.
Require Import InlinedMonoidBSFold.

Require Import Simple.
Require Import SimpleFold.

Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Foldable.

Require Import GHC.List.
Require GHC.Char.

Require Import GHC.Base.

Definition eq_CharType (x : CharType) (y:CharType) :=
  match x , y with 
    | IsSpace , IsSpace => true
    | NotSpace, NotSpace => true
    | _ , _ => false
  end.

Instance Eq_CharType : Eq_ CharType := eq_default eq_CharType.

Fixpoint eq_flux (x : Flux) (y: Flux) : bool :=
  match x , y with 
  | Mk_Flux c1 i c2 , Mk_Flux d1 j d2 => 
    (c1 == d1) && (i == j) && (c2 == d2)
  | Unknown , Unknown => true
  | _ , _ => false 
  end.

Instance Eq_Flux : Eq_ Flux := eq_default eq_flux.

Instance EqLaws_CharType : EqLaws CharType. Admitted.
Instance EqLaws_Flux : EqLaws Flux. Admitted.

Instance SemigroupLaws_Flux : SemigroupLaws Flux := {}.
Proof.
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

Instance Lawful_Flux : MonoidLaws Flux := {}.
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

Instance EqExact_Counts : EqExact Counts. Admitted.

Instance SemigroupLaws_Counts : SemigroupLaws Counts := {}.
Proof.
  intros x y z.
  destruct x eqn:Hx; destruct y eqn:Hy; destruct z eqn:Hz;  
    unfold op_zlzlzgzg__, Semigroup__Counts, Types.Semigroup__Counts_op_zlzlzgzg__; simpl.
  unfold op_zeze__, Eq_Counts, eq_default, op_zeze____,eq_counts .
Admitted.

Instance MonoidLaws_Counts : MonoidLaws Counts := {}.
Proof.
  + intros x. destruct x. apply Eq_reflI. reflexivity.
  + intros x. destruct x. apply Eq_reflI. 
  unfold mappend, mempty, Monoid__Counts , mappend__ , mempty__, Types.Monoid__Counts_mempty . 
  unfold Types.Monoid__Counts_mappend.
  unfold op_zlzlzgzg__, Semigroup__Counts, Types.Semigroup__Counts_op_zlzlzgzg__; simpl.
  f_equal. omega. admit. omega.
  + intros x y. apply Eq_reflI. reflexivity.
  + intros x. apply Eq_reflI. reflexivity.
Admitted.


Lemma to_from : forall c, toTuple (fromTuple c) = c.
Proof.
  destruct c. destruct p. reflexivity.
Qed.

Opaque Z.add.

Instance EqExactFlux : EqExact Flux := {}.
Proof. intros x y.
       apply iff_reflect. split. intro h. subst. apply Eq_reflI. reflexivity.
Admitted.  

Require Import Proofs.Data.OldList.

Lemma eqIsEq : forall {A:Type} `{EqExact A}{x}{y}, ((x == y) = true) -> (x = y).
Proof. intros. Admitted.

Lemma Counts_assoc : forall x y z : Counts, ((x <<>> (y <<>> z)) = ((x <<>> y) <<>> z)).
  intros x y z. eapply eqIsEq. eapply semigroup_assoc; eauto.
Qed.


Lemma assoc : forall s m2,
  (m2 <<>> (fromTuple (Stupid.length s, Stupid.length (OldList.words s), Stupid.length (OldList.lines s)))) =
  (BL.foldl' (fun (a : Counts) (b : Char) => a <<>> countChar b) (mempty <<>> m2) (BL.pack s)).
Proof.
  induction s; intro m2; autorewrite with hs_simpl.
  + rewrite BL.ByteString_foldl_nil. admit.
  + rewrite BL.ByteString_foldl_cons.
    rewrite <- Counts_assoc.    
    rewrite <- IHs.
    rewrite <- Counts_assoc.
    f_equal.
    unfold countChar. unfold flux.
    destruct (isSpace a) eqn:AS.
    destruct (a == Types.newline) eqn:AN.
    ++ admit. (* can't be both space and newline *)
    ++ simpl. rewrite AN.
       destruct break as [ys zs] eqn:B.
       simpl.
       unfold op_zlzlzgzg__, Semigroup__Counts, Types.Semigroup__Counts_op_zlzlzgzg__; simpl.
       unfold op_zlzlzgzg__, Semigroup__Flux, Types.Semigroup__Flux_op_zlzlzgzg__; simpl.
       f_equal.
       destruct s. simpl in *. inversion B. simpl. admit.
       inversion B.
       hs_simpl.
Admitted.

Lemma stupid_inlined : forall s, toTuple (stupidCountFile s) = toTuple (countFile (BL.pack s)).
Proof.
  unfold stupidCountFile, countFile in *.
  intro s. 
  induction s;
  autorewrite with hs_simpl.
  + rewrite BL.ByteString_foldl_nil. reflexivity.
  + rewrite BL.ByteString_foldl_cons.
Admitted.    
                                                              

