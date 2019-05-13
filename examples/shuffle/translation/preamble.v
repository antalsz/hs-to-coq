Require Coq.Arith.Wf_nat.

Local Obligation Tactic := idtac.

Local Ltac solve_riffle :=
  solve [ apply Wf.measure_wf, Wf_nat.lt_wf
        | Tactics.program_simpl; simpl; rewrite PeanoNat.Nat.add_succ_r; auto ].

Ltac solve_shuffleLength_start halve length_halve solve1 solve2 :=
  try solve [apply Wf.measure_wf, Wf_nat.lt_wf];
  Tactics.program_simpl; try easy;
  match goal with H : (?half1,?half2) = halve _ ?arg_0__ |- _ =>
    generalize (length_halve _ arg_0__);
    rewrite <-H;
    intros [def_length1 def_length2];
    (* (rewrite def_length1 || rewrite def_length2); simpl; *)
    solve [solve1 arg_0__ def_length1 | solve2 arg_0__ def_length2]
  end.

Ltac solve_shuffleLength_half1 arg_0__ def_length1 :=
  rewrite def_length1; simpl;
  destruct arg_0__ as [|head0 tail0]; simpl; try easy;
  apply Lt.lt_n_S, PeanoNat.Nat.lt_div2;
  destruct tail0; simpl; [|apply PeanoNat.Nat.lt_0_succ];
  match goal with H : forall x, (cons x nil) <> (cons ?h nil) |- _ => specialize (H h) end;
  contradiction.

Ltac solve_shuffleLength_half2 arg_0__ def_length2 :=
  rewrite def_length2;
  apply PeanoNat.Nat.lt_div2;
  now destruct arg_0__; simpl; [|apply PeanoNat.Nat.lt_0_succ].

Ltac solve_shuffleLength halve length_halve :=
  solve_shuffleLength_start halve length_halve solve_shuffleLength_half1 solve_shuffleLength_half2.
