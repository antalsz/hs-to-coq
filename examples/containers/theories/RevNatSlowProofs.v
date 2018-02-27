Require Import NArith.NArith.
Require Import ZArith.ZArith.
Require Import Bool.Bool.
Require Import Psatz.

Definition WIDTH : N := 64%N.

Local Definition revNat n := (N.lor
   (N.shiftr
      (N.lor
         (N.land
            (N.shiftr
               (N.lor
                  (N.land
                     (N.shiftr
                        (N.lor
                           (N.land
                              (N.shiftr
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2))) (Z.to_N 4))
                              (Z.to_N 1085102592571150095))
                           (N.shiftl
                              (N.land
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2)))
                                 (Z.to_N 1085102592571150095)) (Z.to_N 4)))
                        (Z.to_N 8)) (Z.to_N 71777214294589695))
                  (N.shiftl
                     (N.land
                        (N.lor
                           (N.land
                              (N.shiftr
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2))) (Z.to_N 4))
                              (Z.to_N 1085102592571150095))
                           (N.shiftl
                              (N.land
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2)))
                                 (Z.to_N 1085102592571150095)) (Z.to_N 4)))
                        (Z.to_N 71777214294589695)) (Z.to_N 8))) (Z.to_N 16))
            (Z.to_N 281470681808895))
         (N.shiftl
            (N.land
               (N.lor
                  (N.land
                     (N.shiftr
                        (N.lor
                           (N.land
                              (N.shiftr
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2))) (Z.to_N 4))
                              (Z.to_N 1085102592571150095))
                           (N.shiftl
                              (N.land
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2)))
                                 (Z.to_N 1085102592571150095)) (Z.to_N 4)))
                        (Z.to_N 8)) (Z.to_N 71777214294589695))
                  (N.shiftl
                     (N.land
                        (N.lor
                           (N.land
                              (N.shiftr
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2))) (Z.to_N 4))
                              (Z.to_N 1085102592571150095))
                           (N.shiftl
                              (N.land
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2)))
                                 (Z.to_N 1085102592571150095)) (Z.to_N 4)))
                        (Z.to_N 71777214294589695)) (Z.to_N 8)))
               (Z.to_N 281470681808895)) (Z.to_N 16))) (Z.to_N 32))
   (N.shiftl
      (N.lor
         (N.land
            (N.shiftr
               (N.lor
                  (N.land
                     (N.shiftr
                        (N.lor
                           (N.land
                              (N.shiftr
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2))) (Z.to_N 4))
                              (Z.to_N 1085102592571150095))
                           (N.shiftl
                              (N.land
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2)))
                                 (Z.to_N 1085102592571150095)) (Z.to_N 4)))
                        (Z.to_N 8)) (Z.to_N 71777214294589695))
                  (N.shiftl
                     (N.land
                        (N.lor
                           (N.land
                              (N.shiftr
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2))) (Z.to_N 4))
                              (Z.to_N 1085102592571150095))
                           (N.shiftl
                              (N.land
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2)))
                                 (Z.to_N 1085102592571150095)) (Z.to_N 4)))
                        (Z.to_N 71777214294589695)) (Z.to_N 8))) (Z.to_N 16))
            (Z.to_N 281470681808895))
         (N.shiftl
            (N.land
               (N.lor
                  (N.land
                     (N.shiftr
                        (N.lor
                           (N.land
                              (N.shiftr
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2))) (Z.to_N 4))
                              (Z.to_N 1085102592571150095))
                           (N.shiftl
                              (N.land
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2)))
                                 (Z.to_N 1085102592571150095)) (Z.to_N 4)))
                        (Z.to_N 8)) (Z.to_N 71777214294589695))
                  (N.shiftl
                     (N.land
                        (N.lor
                           (N.land
                              (N.shiftr
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2))) (Z.to_N 4))
                              (Z.to_N 1085102592571150095))
                           (N.shiftl
                              (N.land
                                 (N.lor
                                    (N.land
                                       (N.shiftr
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1))) (Z.to_N 2))
                                       (Z.to_N 3689348814741910323))
                                    (N.shiftl
                                       (N.land
                                          (N.lor
                                             (N.land (N.shiftr n (Z.to_N 1))
                                                (Z.to_N 6148914691236517205))
                                             (N.shiftl
                                                (N.land n
                                                   (Z.to_N
                                                      6148914691236517205))
                                                (Z.to_N 1)))
                                          (Z.to_N 3689348814741910323))
                                       (Z.to_N 2)))
                                 (Z.to_N 1085102592571150095)) (Z.to_N 4)))
                        (Z.to_N 71777214294589695)) (Z.to_N 8)))
               (Z.to_N 281470681808895)) (Z.to_N 16))) (Z.to_N 32))
 mod 2 ^ 64)%N.

(* This proof of revNat_or could be used
   in a more efficient proof of revNat_spec, where
   we break the input down in a [N.lorg] of powers of two,
   and then use computation on these powers of two.
 *)

(*
Definition hidden_lor := N.lor.

Lemma land_hidden_lor:
  forall a b x,
  N.land (hidden_lor a b) x = hidden_lor (N.land a x) (N.land b x).
Proof.
  intros.
  unfold hidden_lor.
  apply N.bits_inj_iff; intro i.
  repeat first [rewrite N.land_spec | rewrite N.lor_spec].
  destruct (N.testbit a i), (N.testbit b i), (N.testbit x i); reflexivity.
Qed.

Lemma lor_hidden_lor:
  forall a b c d,
  N.lor (hidden_lor a b) (hidden_lor c d) = hidden_lor (N.lor a c) (N.lor b d).
Proof.
  intros.
  unfold hidden_lor.
  apply N.bits_inj_iff; intro i.
  repeat first [rewrite N.lor_spec | rewrite N.lxor_spec].
  destruct (N.testbit a i), (N.testbit b i), (N.testbit c i), (N.testbit d i); reflexivity.
Qed.

Lemma shiftr_hidden_lor:
  forall a b n,
  N.shiftr (hidden_lor a b) n = hidden_lor (N.shiftr a n) (N.shiftr b n).
Proof.
  exact N.shiftr_lor.
Qed.

Lemma shiftl_hidden_lor:
  forall a b n,
  N.shiftl (hidden_lor a b) n = hidden_lor (N.shiftl a n) (N.shiftl b n).
Proof.
  exact N.shiftl_lor.
Qed.


Lemma revNat_or:
  forall a b,
  revNat (N.lor a b) = N.lor (revNat a) (revNat b).
Proof.
  intros.
  fold hidden_lor.
  unfold revNat.
  repeat match goal with
  | [ |- _ = hidden_lor (N.lor _ _) (N.lor _ _) ] =>
      rewrite <- lor_hidden_lor; f_equal
  | [ |- _ = hidden_lor (N.land _ _) (N.land _ _) ] =>
      rewrite <- land_hidden_lor; f_equal
  | [ |- _ = hidden_lor (N.shiftr _ _) (N.shiftr _ _) ] =>
      rewrite <- shiftr_hidden_lor; f_equal
  | [ |- _ = hidden_lor (N.shiftl _ _) (N.shiftl _ _) ] =>
      rewrite <- shiftl_hidden_lor; f_equal
  end.
Qed.
*)

Lemma N_shiftl_spec_eq:
  forall n i j,
  N.testbit (N.shiftl n i) j =
    (if j <? i then false else N.testbit n (j - i))%N.
Proof.
  intros.
  destruct (N.ltb_spec j i).
  * apply N.shiftl_spec_low; assumption.
  * apply N.shiftl_spec_high'; assumption.
Qed.

Lemma revNat_spec:
  forall n i, (i < WIDTH)%N ->
  N.testbit (revNat n) i = N.testbit n (WIDTH - 1 - i)%N.
Proof.
  intros.
  unfold WIDTH in *.
  Ltac next :=
    match goal with [ H : (?i < ?n)%N |- _ ] =>
      let m := eval simpl in (n - 1)%N in
      idtac "Now solving i =" m;
      assert (Hor : (i = m \/ i < m)%N) by lia; clear H; destruct Hor
    end.

  Ltac rewrite_land_smart := 
      match goal with [ |- context [N.testbit (N.land ?x ?y) ?i] ] =>
        rewrite N.land_spec;
        simpl (N.testbit y i); (* The right side is always constant, so simplify right away *)
        rewrite andb_false_r || rewrite andb_true_r
      end.

  unfold revNat.
  
  rewrite N.mod_pow2_bits_low by assumption.

  Ltac solve :=
      subst;
      repeat ltac:(simpl N.add; simpl N.sub; simpl N.ltb; first
             [ rewrite andb_false_r
             | rewrite andb_true_r
             | rewrite orb_false_r 
             | rewrite N.lor_spec
             | rewrite_land_smart
             | rewrite N.shiftr_spec by (intro Htmp; inversion Htmp)
             | rewrite N_shiftl_spec_eq
             ]);
      reflexivity.
  Time do 64 (next; [solve|]).
  apply N.nlt_0_r in H. contradiction.
Qed.


(* Only true due to the edit which adds a [_ % 2^64] at the end *)
Lemma isBitMask0_revNat:
  forall n, (revNat n < 2^WIDTH)%N.
Proof.
  intros.
  apply N.mod_lt.
  intro. inversion H.
Qed.