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

Lemma to_from : forall c, toTuple (fromTuple c) = c.
Proof.
  destruct c. destruct p. reflexivity.
Qed.

Axiom words_nil : OldList.words nil = nil.
Axiom lines_nil : OldList.lines nil = nil.

Axiom words_cons : forall c s, OldList.words (cons c s) = 
                   if Types.isSpaceChar8 c then OldList.words s
                   else let (w, s'') := break Types.isSpaceChar8 s in 
                        (cons w (OldList.words s'')).
Axiom lines_cons : forall c s, OldList.lines (cons c s) = 
                          (fun x => match x with | (pair h t) => cons h t end) 
                           (match break (fun x => x == Types.newline) (cons c s) with
                                    | (l, s') => (l, match s' with 
                                                   | nil => nil
                                                   | cons _ s'' => OldList.lines s''
                                                   end)
                            end).
Hint Rewrite words_nil lines_nil words_cons lines_cons : hs_simpl.


Opaque Z.add.

Instance EqExactFlux : EqExact Flux := {}.
Proof. intros x y.
       apply iff_reflect. split. intro h. subst. apply Eq_reflI. reflexivity.
Admitted.  


Check Eq_eq.
     

Lemma stupid_inlined : forall s, toTuple (stupidCountFile s) = toTuple (countFile (BL.pack s)).
Proof.
  induction s;
  unfold stupidCountFile, countFile;
  autorewrite with hs_simpl.
  + rewrite ByteString_foldl_nil. reflexivity.
  + rewrite ByteString_foldl_cons.
    destruct (isSpaceChar8 a) eqn:S.
    ++ Check monoid_left_id.
      rewrite monoid_left_id.
       unfold break.
       assert (a == newline = false). admit.
       rewrite H.
       simpl. destruct s. simpl.
       
    unfold Base.mempty, Types.Monoid__Counts, Base.mempty__ , Types.Monoid__Counts_mempty. simpl.
    unfold Base.mempty, Types.Monoid__Flux, Base.mempty__ , Types.Monoid__Flux_mempty. 
    
                                                              

Lemma simple_simpleFold : 
  forall s, simpleCountFile s = stupidCountFile s.
Proof.
  induction s.
  + unfold stupidCountFile. simpl.    
    unfold simpleCountFile. 
    hs_simpl. simpl.
    unfold Foldable.foldMap, Foldable.Foldable__list , Foldable.foldMap__, Foldable.Foldable__list_foldMap .
    simpl.
    unfold Base.mempty, Types.Monoid__Counts, Base.mempty__ , Types.Monoid__Counts_mempty. simpl.
    unfold Base.mempty, Types.Monoid__Flux, Base.mempty__ , Types.Monoid__Flux_mempty. 
    admit.
  + unfold stupidCountFile, simpleCountFile.
    hs_simpl.
    unfold Foldable.foldMap, Foldable.Foldable__list , Foldable.foldMap__, Foldable.Foldable__list_foldMap .
    hs_simpl.
    unfold Types.fromTuple.
    admit.
Admitted.

