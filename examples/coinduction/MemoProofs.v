Require Import Coq.NArith.BinNat.
Require Import GHC.Base.
Require Import Psatz.

Require Import Memo.

Set Bullet Behavior "Strict Subproofs".
Open Scope N_scope.

Lemma lookupTrie_eq {a} (t : NatTrie a) n:
  lookupTrie t n =  match t with
    | TrieNode here div2 minus1div2 =>
        if Sumbool.sumbool_of_bool (n =? 0)         then here else
        if Sumbool.sumbool_of_bool (GHC.Real.odd n) then lookupTrie minus1div2 (GHC.Real.div n 2)
                                                    else lookupTrie div2 (GHC.Real.div n 2)
    end.
Proof.
  intros.
  unfold lookupTrie at 1, lookupTrie_func at 1.
  destruct t.
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.


Program Fixpoint
  memo_spec a (f : N -> a) x {measure x (N.lt)}:
  lookupTrie (mkTrie f) x = f x
  := _.
Next Obligation.
  rewrite lookupTrie_eq.
  simpl.
  repeat destruct (Sumbool.sumbool_of_bool).
  * rewrite N.eqb_eq in *; subst.
    reflexivity.
  * rewrite N.eqb_neq in *.
    rewrite memo_spec by (apply N.div_lt; lia).
    unfold op_z2218U__.
    f_equal.
    unfold Real.odd, Real.even, Real.rem, Real.instance__Integral_Word, fromInteger, Num_Word__ in e0.
    simpl Z.to_N in e0.
    rewrite negb_true_iff in e0.
    apply N.eqb_neq in e0.
    pose proof (N.mod_upper_bound x 2).
    pose proof (N.div_mod' x 2).
    remember (x mod 2) as y.
    lia.
  * rewrite N.eqb_neq in *.
    rewrite memo_spec by (apply N.div_lt; lia).
    unfold op_z2218U__.
    f_equal.
    unfold Real.odd, Real.even, Real.rem, Real.instance__Integral_Word, fromInteger, Num_Word__ in e0.
    simpl Z.to_N in e0.
    rewrite negb_false_iff in e0.
    apply N.eqb_eq in e0.
    pose proof (N.mod_upper_bound x 2).
    pose proof (N.div_mod' x 2).
    lia.
Qed.
Next Obligation.
  apply Wf.measure_wf.
  apply Coq.NArith.BinNat.N.lt_wf_0.
Qed.

Lemma cachedFib_slowFib:
  forall n, cachedFib n = slowFib n.
Proof. apply memo_spec. Qed.

Time Eval vm_compute in slowFib 25. (* Finished transaction in 2.248 secs *)
Time Eval vm_compute in slowFib 25. (* Finished transaction in 2.233 secs *)
Time Eval vm_compute in cachedFib 25. (* Finished transaction in 2.203 secs *)
Time Eval vm_compute in cachedFib 25. (* Finished transaction in 0. secs *)
Time Eval vm_compute in cachedFib 26. (* Finished transaction in 3.579 secs *)
Time Eval vm_compute in cachedFib 26. (* Finished transaction in 0. secs *)

