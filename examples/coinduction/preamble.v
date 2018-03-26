Require Coq.NArith.BinNat.
Require Psatz.


(* There is [Coq.NArith.BinNat.N.lt_wf_0], but it is Opauqe, so we cannot
   compute with Program Fixpoint that recurse on [N].
   Until this is fixed (in https://github.com/coq/coq/pull/7060), we
   we reprove this lemma and close it with [Defined].
*)
Require Import Coq.NArith.BinNat.
Theorem N_lt_wf : well_founded N.lt.
Proof.
  assert (well_founded (fun n1 n2 => (N.to_nat n1) < (N.to_nat n2)))
    by (apply Wf_nat.well_founded_ltof).

  intro x.
  specialize (H x).
  induction H.
  constructor.
  intros y Hy.
  apply H0.
  Psatz.lia.
Defined.

Ltac solve_lookupTrie :=
  Coq.Program.Tactics.program_simplify;
  try apply Wf.measure_wf;
  try apply N_lt_wf;
  try match goal with  H : _  = false |- _ => apply Coq.NArith.BinNat.N.eqb_neq in H end;
  apply Coq.NArith.BinNat.N.div_lt;
  Psatz.lia.

Ltac solve_fib := Coq.Program.Tactics.program_simplify;
  try apply N_lt_wf;
  repeat match goal with  H : _ = false |- _ => apply Coq.NArith.BinNat.N.eqb_neq in H end;
  Psatz.lia.
