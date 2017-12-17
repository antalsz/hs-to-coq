Require Coq.ZArith.Zcomplements.
Require Coq.Numbers.BinNums.

Definition shiftLL (n: Nat) (s : BinInt.Z) : Nat :=
	Coq.NArith.BinNat.N.shiftl n (Coq.ZArith.BinInt.Z.to_N s).
Definition shiftRL (n: Nat) (s : BinInt.Z) : Nat :=
	Coq.NArith.BinNat.N.shiftr n (Coq.ZArith.BinInt.Z.to_N s).

Definition highestBitMask (n: Nat) : Nat := match n with
 | Coq.Numbers.BinNums.N0 => Coq.Numbers.BinNums.N0
 | Coq.Numbers.BinNums.Npos p => Coq.Numbers.BinNums.Npos (Coq.ZArith.Zcomplements.floor_pos p) end.

Instance Bits__Word : Bits.Bits Num.Word. Admitted.

Fixpoint size_nat (t : IntSet) : nat :=
  match t with
  | Bin _ _ l r => S (size_nat l + size_nat r)%nat
  | Tip _ bm => 0
  | Nil => 0
  end.

Require Omega.
Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

