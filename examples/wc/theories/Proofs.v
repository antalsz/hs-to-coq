Require Import Proofs.Types.
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

Require Import Proofs.Data.OldList.

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
    destruct (Unicode.isSpace a) eqn:AS.
    destruct (a == newline) eqn:AN.
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
