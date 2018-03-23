Require Coq.NArith.BinNat.
Require Psatz.

Ltac solve_lookupTrie :=
  Coq.Program.Tactics.program_simplify;
  try apply Wf.measure_wf;
  try apply Coq.NArith.BinNat.N.lt_wf_0;
  try match goal with  H : _  = false |- _ => apply Coq.NArith.BinNat.N.eqb_neq in H end;
  apply Coq.NArith.BinNat.N.div_lt;
  Psatz.lia.

Ltac solve_fib := Coq.Program.Tactics.program_simplify;
  try apply Coq.NArith.BinNat.N.lt_wf_0;
  repeat match goal with  H : _ = false |- _ => apply Coq.NArith.BinNat.N.eqb_neq in H end;
  Psatz.lia.
