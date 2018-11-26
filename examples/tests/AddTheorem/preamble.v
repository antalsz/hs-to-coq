Require Coq.Arith.Wf_nat.

Ltac solve_oddPositions behead_shrinks :=
  match goal with BEHEAD : cons ?y ?ys = ?behead ?a ?xs |- _ =>
    lapply (@behead_shrinks a xs); [|now destruct xs];
    intros H; etransitivity; [|apply H];
    rewrite <-BEHEAD; simpl;
    apply le_n
  end.
