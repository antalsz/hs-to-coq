Require Import NArith.NArith.
Require Import ZArith.ZArith.
Require Import Bool.Bool.
Require Import Psatz.

Definition WIDTH : N := 64%N.

Local Infix ".&." := N.land (at level 50, no associativity).
Local Infix ".|." := N.lor (at level 50, no associativity).

Local Definition revNat : N -> N :=
  fun x1 =>
    let 'x2 := ((N.shiftr x1 1) .&.(**) 6148914691236517205) .|.(**)
                 (N.shiftl (x1 .&.(**) 6148914691236517205) 1) in
    let 'x3 := ((N.shiftr x2 2) .&.(**) 3689348814741910323) .|.(**)
                 (N.shiftl (x2 .&.(**) 3689348814741910323) 2) in
    let 'x4 := ((N.shiftr x3 4) .&.(**) 1085102592571150095) .|.(**)
                 (N.shiftl (x3 .&.(**) 1085102592571150095) 4) in
    let 'x5 := ((N.shiftr x4 8) .&.(**) 71777214294589695) .|.(**)
                 (N.shiftl (x4 .&.(**) 71777214294589695) 8) in
    let 'x6 := ((N.shiftr x5 16) .&.(**) 281470681808895) .|.(**)
                 (N.shiftl (x5 .&.(**) 281470681808895) 16) in
    (((N.shiftr x6 32) .|.(**) (N.shiftl x6 32)) mod 2 ^ 64)%N.

Inductive Term :=
  | Input : Term
  | Const : N -> Term
  | LAnd : Term -> Term -> Term
  | LOr : Term -> Term -> Term
  | ShiftL : Term -> N -> Term
  | ShiftR : Term -> N -> Term
  | ModPow2 : Term -> N -> Term.

Fixpoint evalTerm (n : N) (t : Term) : N :=
  match t with
  | Input => n
  | Const n => n
  | LAnd t1 t2 => N.land (evalTerm n t1) (evalTerm n t2)
  | LOr  t1 t2 => N.lor  (evalTerm n t1) (evalTerm n t2)  
  | ShiftL t1 s => N.shiftl (evalTerm n t1) s
  | ShiftR t1 s => N.shiftr (evalTerm n t1) s
  | ModPow2 t1 s => (evalTerm n t1 mod 2^s)%N
 end.

Fixpoint checkbit (n : N) (i : N) (t : Term) : bool :=
  match t with
  | Input => N.testbit n i
  | Const c => N.testbit c i
  | LAnd t1 t2 => if checkbit n i t2 then checkbit n i t1 else false
  | LOr  t1 t2 => orb  (checkbit n i t1) (checkbit n i t2)
  | ShiftL t1 s => if (i <? s)%N then false else checkbit n (i - s) t1
  | ShiftR t1 s => checkbit n (i + s) t1
  | ModPow2 t1 s => if (i <? s)%N then checkbit n i t1 else false
 end.

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

Lemma checkbit_correct: forall n i t,
  checkbit n i t = N.testbit (evalTerm n t) i.
Proof.
  intros. revert i. induction t; intros i; simpl.
  * reflexivity.
  * reflexivity.
  * rewrite N.land_spec, IHt1, IHt2.
    destruct (N.testbit (evalTerm n t2) i); rewrite ?andb_true_r, ?andb_false_r; reflexivity.
  * rewrite N.lor_spec, IHt1, IHt2. reflexivity.
  * rewrite N_shiftl_spec_eq, IHt. reflexivity.
  * rewrite N.shiftr_spec, IHt. reflexivity. apply N.le_0_l.
  * destruct (N.ltb_spec i n0). 
    - rewrite N.mod_pow2_bits_low by assumption.
      rewrite IHt. reflexivity.
    - rewrite N.mod_pow2_bits_high by assumption.
      reflexivity.
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

  unfold revNat.
  
  Ltac toTerm n x :=
    let rec go x :=
       match x with
        | (?y mod 2^?k)%N => let t1 := go y in constr:(ModPow2 t1 k)
        | N.land ?e1 ?e2 =>  let t1 := go e1 in let t2 := go e2 in constr:(LAnd t1 t2)
        | N.lor  ?e1 ?e2 =>  let t1 := go e1 in let t2 := go e2 in constr:(LOr t1 t2)
        | N.shiftr ?e1 ?s => let t1 := go e1 in let c := eval simpl in s in constr:(ShiftR t1 c)
        | N.shiftl ?e1 ?s => let t1 := go e1 in let c := eval simpl in s in constr:(ShiftL t1 c)
        | n => constr:(Input)
        | _ => let c := eval simpl in x in constr:(Const c)
       end
     in go x.

  lazymatch goal with |- N.testbit ?exp i = ?rhs =>
    let tm := toTerm n exp in
    change (N.testbit (evalTerm n tm) i = rhs)
   end.
  rewrite <- checkbit_correct.
  do 64 (next; [subst; simpl checkbit; rewrite ?orb_false_r; reflexivity|]).
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