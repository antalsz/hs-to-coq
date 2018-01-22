Require Import GHC.Base.
Import Notations.
Require Import GHC.Num.
Import Notations.

From mathcomp Require Import ssrbool ssreflect.

Local Open Scope Z_scope.

(** This should be in a separate file, but let's keep it here for
    convenience for now. *)
Section Int_And_Z.
  Variables a b : Int.

  Lemma Int_plus_is_Z_plus :
    a GHC.Num.+ b = (a + b).
  Proof. rewrite /_GHC.Num.+_. reflexivity. Qed.

  Lemma Int_minus_is_Z_minus :
    a GHC.Num.- b = (a - b).
  Proof. rewrite /_GHC.Num.-_. reflexivity. Qed.

  Lemma Int_mult_is_Z_mult :
    a GHC.Num.* b = (a * b).
  Proof. rewrite /_GHC.Num.*_. reflexivity. Qed.

  Lemma Int_lt_is_Z_lt :
    a GHC.Base.< b = (a <? b).
  Proof. rewrite /_GHC.Base.<_. reflexivity. Qed.

  Lemma Int_le_is_Z_le :
    a GHC.Base.<= b = (a <=? b).
  Proof. rewrite /_GHC.Base.<=_. reflexivity. Qed.

  Lemma Int_gt_is_Z_gt :
    a GHC.Base.> b = (b <? a).
  Proof. rewrite /_GHC.Base.>_. reflexivity. Qed.

  Lemma Int_ge_is_Z_ge :
    a GHC.Base.>= b = (b <=? a).
  Proof. rewrite /_GHC.Base.>=_. reflexivity. Qed.

  Lemma Int_eq_is_Z_eq :
    a GHC.Base.== b = (Z.eqb a b).
  Proof. rewrite /_GHC.Base.==_. reflexivity. Qed.

  Lemma Int_is_Z : forall a : Z,
      # a = a.
  Proof. reflexivity. Qed.

End Int_And_Z.

Ltac rewrite_Int :=
  repeat (rewrite ?Int_plus_is_Z_plus ?Int_minus_is_Z_minus
                  ?Int_mult_is_Z_mult
                  ?Int_lt_is_Z_lt ?Int_le_is_Z_le
                  ?Int_ge_is_Z_ge ?Int_gt_is_Z_gt
                  ?Int_eq_is_Z_eq ?Int_is_Z).

Section ZReflect.
  Variables a b : Z.

  Lemma Z_eqP : reflect (a = b) (a =? b).
  Proof.
    destruct (a =? b) eqn:Hab; constructor; move: Hab.
    - move /Z.eqb_eq  =>//.
    - move /Z.eqb_neq =>//.
  Qed.

  Lemma Z_ltP : reflect (a < b) (a <? b).
  Proof.
    destruct (a <? b) eqn:Hab; constructor; move: Hab.
    - move /Z.ltb_lt =>//.
    - move /Z.ltb_nlt =>//.
  Qed.
End ZReflect.

Arguments Z_eqP {a} {b}.
Arguments Z_ltP {a} {b}.

Lemma Z_gtP { a b }: reflect (b < a) (a >? b).
Proof. rewrite Z.gtb_ltb. apply Z_ltP. Qed.
